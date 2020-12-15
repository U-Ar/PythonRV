#!/usr/bin/env python
# coding: utf-8

# not rd, rs ... xori rd, rs1, -1
# snez(not equal zero) rd, rs ... sltu rd, x0, rs
# j(plain unconditional jump) ... jal x0
# jalのreturn address registerはx1，alternate link registerはx5
# 
# unsignedで正しくsignextensionを行うには元のビット数によるsignedでマイナスならきっちりマイナスにしたうえでやる必要がある
# 
# 
# プログラムはバイナリの形で与えられる
# もらったやつは，0x1000から始まるアドレスのDRAMにアドレスを一つずつ増やしながら入れていく
# pcは0x1000で初期化してメモリを読みながら命令を実行する

# In[ ]:


from enum import IntEnum,auto
class Mode(IntEnum):
    M = 0
    S = 2
    U = 3
class Interrupt(IntEnum):
    user_software_interrupt = 0
    supervisor_software_interrupt = 1
    machine_software_interrupt = 3
    user_timer_interrupt = 4
    supervisor_timer_interrupt = 5
    machine_timer_interrupt = 7
    user_external_interrupt = 8
    supervisor_esternal_interrupt = 9
    machine_external_interrupt = 11
class Exception(IntEnum):
    instruction_address_misaligned = 0
    instruction_access_fault = 1
    illegal_instruction = 2
    breakpoint = 3
    load_address_misaligned = 4
    load_access_fault = 5
    store_address_misaligned = 6
    store_access_fault = 7
    environment_call_from_umode = 8
    environment_call_from_smode = 9
    environment_call_from_mmode = 11
    instruction_page_fault = 12
    load_page_fault = 13
    store_page_fault = 15
class MemoryAccessType(IntEnum):
    instruction = 0
    load = 1
    store = 2
    
    
    
    
    


# In[5]:



opcodes = {
    "addi",
    "slti",
    "sltiu",
    "andi",
    "ori",
    "xori",
    "slli",
    "srli",
    "srai",
    "lui",
    "auipc",
    "add",
    "slt",
    "sltu",
    "and",
    "or",
    "xor",
    "sll",
    "srl",
    "sub",
    "sra",
    "nop",
    "jal",
    "jalr",
    "beq",
    "bne",
    "blt",
    "bltu",
    "bge",
    "bgeu",
    "load",
    "store",
    "fence",
    "ecall",
    "ebreak"
}

MAX_64 = 2**64
MAX_32 = 2**32
reg = [0 for i in range(32)]
pc = 0
mode = Mode.M
finished = False
pc_updated = False

def at(rd,i):
    return (rd & (1<<i)) >> i
def fromto(rd,l,r):
    if l < r or l > 31 or r < 0:
        raise ValueError("invalid argument of range of register")
    return (rd >> r) % (1 << (l-r+1))
def signed(i,bit):
    if (i & (1 << (bit-1))) > 0:
        return -1 * (((1<<bit)-1) ^ (i-1))
    return i
def unsigned(i,bit):
    if i < 0:
        return (((1<<bit)-1) ^ (-1*i)) + 1
    return i
def extend(i,f,t):
    return unsigned(signed(i,f),t)
def write_reg(rd,i):
    if rd != 0:
        reg[rd] = i
def write_csr(idx,msb,lsb,imm):
    tmp = csr[idx]
    tmp -= tmp & ((1<<(msb+1)) - (1<<lsb))
    csr[idx] = tmp | fromto(imm,msb-lsb,0) << lsb
def update_pc(new):
    global pc, pc_updated
    pc_updated = True
    pc = new


# In[1]:


mem = dict()
ADDR_BASE = 0x80000000
ADDR_FROMHOST = 0x1000 + ADDR_BASE
ADDR_TOHOST = 0x1000 + ADDR_FROMHOST
tohost_data = 0
fromhost_data = 0

def store_byte(addr,byte):
    mem[addr]   = byte
def store_hword(addr,hword):
    mem[addr+1]   = (hword&0xff00)>>8
    mem[addr] = hword&0x00ff
def store_word(addr,word):
    global finished, tohost_data
    if addr == ADDR_TOHOST:
        tohost_data = word
        finished = True
    mem[addr+3]   = (word&0xff000000)>>24
    mem[addr+2] = (word&0x00ff0000)>>16
    mem[addr+1] = (word&0x0000ff00)>>8
    mem[addr] = (word&0x000000ff)
def store_dword(addr,word):
    global finished, tohost_data
    if addr == ADDR_TOHOST:
        tohost_data = word
        finished = True
    mem[addr+7]   = (word&0xff00000000000000)>>56
    mem[addr+6] = (word&0x00ff000000000000)>>48
    mem[addr+5] = (word&0x0000ff0000000000)>>40
    mem[addr+4] = (word&0x000000ff00000000)>>32
    mem[addr+3] = (word&0x00000000ff000000)>>24
    mem[addr+2] = (word&0x0000000000ff0000)>>16
    mem[addr+1] = (word&0x000000000000ff00)>>8
    mem[addr] = (word&0x00000000000000ff)
def load_byte(addr):
    if addr in mem:
        return mem[addr]
    return 0
def load_hword(addr):
    d1 = load_byte(addr+1)
    d2 = load_byte(addr)
    return (d1 << 8) | d2
def load_word(addr):
    d1 = load_hword(addr+2)
    d2 = load_hword(addr)
    return (d1 << 16) | d2
def load_dword(addr):
    d1 = load_word(addr+4)
    d2 = load_word(addr)
    return (d1 << 32) | d2

def _lb(code):
    rd,rs1,imm = itype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.load)
    write_reg(rd,extend(load_byte(pa),8,64))
def _lbu(code):
    rd,rs1,imm = itype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.load)
    write_reg(rd,load_byte(pa))
def _lh(code):
    rd,rs1,imm = itype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.load)
    write_reg(rd,extend(load_hword(pa),16,64))
def _lhu(code):
    rd,rs1,imm = itype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.load)
    write_reg(rd,load_hword(pa))
def _lw(code):
    rd,rs1,imm = itype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.load)
    write_reg(rd,extend(load_word(pa),32,64))
def _lwu(code):
    rd,rs1,imm = itype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.load)
    write_reg(rd,load_word(pa))
def _ld(code):
    rd,rs1,imm = itype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.load)
    write_reg(rd,load_dword(pa))
    
def _sb(code):
    rs1,rs2,imm = stype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.store)
    store_byte(pa,reg[rs2]&0xff)
def _sh(code):
    rs1,rs2,imm = stype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.store)
    store_hword(pa,reg[rs2]&0xffff)
def _sw(code):
    rs1,rs2,imm = stype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.store)
    store_word(pa,reg[rs2]&0xffffffff)
def _sd(code):
    rs1,rs2,imm = stype(code)
    pa = translate_addr(reg[rs1]+signed(imm,12),MemoryAccessType.store)
    store_dword(pa,reg[rs2])


# # CSR

# In[6]:


from enum import IntEnum,auto
class Csr_index(IntEnum):
    ustatus = 0
    uie = auto()
    utvec = auto()
    uscratch = auto()
    uepc = auto()
    ucause = auto()
    utval = auto()
    uip = auto()
    fflags = auto()
    frm = auto()
    fcsr = auto()
    cycle = auto()
    time = auto()
    instret = auto()
    
    sstatus = auto()
    sedeleg = auto()
    sideleg = auto()
    sie = auto()
    stvec = auto()
    scounteren = auto()
    sscratch = auto()
    sepc = auto()
    scause = auto()
    stval = auto()
    sip = auto()
    satp = auto()
    
    misa = auto()
    mvendorid = auto()
    marchid = auto()
    mimpid = auto()
    mhartid = auto()
    mstatus = auto()
    mtvec = auto()
    medeleg = auto()
    mideleg = auto()
    mip = auto()
    mie = auto()
    mtime = auto()
    mtimecmp = auto()
    mcounteren = auto()
    mscratch = auto()
    mepc = auto()
    mcause = auto()
    mtval = auto()
    
    pmpcfg0 = auto()
    pmpcfg1 = auto()
    pmpcfg2 = auto()
    pmpcfg3 = auto()
    pmpaddr0 = auto()
    pmpaddr1 = auto()
    pmpaddr2 = auto()
    pmpaddr3 = auto()
    pmpaddr4 = auto()
    pmpaddr5 = auto()
    pmpaddr6 = auto()
    pmpaddr7 = auto()
    pmpaddr8 = auto()
    pmpaddr9 = auto()
    pmpaddr10 = auto()
    pmpaddr11 = auto()
    pmpaddr12 = auto()
    pmpaddr13 = auto()
    pmpaddr14 = auto()
    pmpaddr15 = auto()
    
    mcycle = auto()
    minstret = auto()
    mcountinhibit = auto()
    mhpmevent3 = auto()
    
    tselect = auto()
    tdata1 = auto()
    tdata2 = auto()
    tdata3 = auto()
    
    dcsr = auto()
    dpc = auto()
    dscratch0 = auto()
    dscratch1 = auto()
    
    invalid = auto()
    
def get_csr_index(d):
    if d == 0x000:
        return Csr_index.ustatus
    elif d == 0x004:
        return Csr_index.uie
    elif d == 0x005:
        return Csr_index.utvec
    elif d == 0x040:
        return Csr_index.uscratch
    elif d == 0x041:
        return Csr_index.uepc
    elif d == 0x042:
        return Csr_index.ucause
    elif d == 0x043:
        return Csr_index.utval
    elif d == 0x044:
        return Csr_index.uip
    elif d == 0x001:
        return Csr_index.fflags
    elif d == 0x002:
        return Csr_index.frm
    elif d == 0x003:
        return Csr_index.fcsr
    
    elif d == 0xc00:
        return Csr_index.cycle
    elif d == 0xc01:
        return Csr_index.time
    elif d == 0xc02:
        return Csr_index.instret
    
    elif d == 0x100:
        return Csr_index.sstatus
    elif d == 0x102:
        return Csr_index.sedeleg
    elif d == 0x103:
        return Csr_index.sideleg
    elif d == 0x104:
        return Csr_index.sie
    elif d == 0x105:
        return Csr_index.stvec
    elif d == 0x106:
        return Csr_index.scounteren
    elif d == 0x140:
        return Csr_index.sscratch
    elif d == 0x141:
        return Csr_index.sepc
    elif d == 0x142:
        return Csr_index.scause
    elif d == 0x143:
        return Csr_index.stval
    elif d == 0x144:
        return Csr_index.sip
    elif d == 0x180:
        return Csr_index.satp
    
    elif d == 0xf11:
        return Csr_index.mvendorid
    elif d == 0xf12:
        return Csr_index.marchid
    elif d == 0xf13:
        return Csr_index.mimpid
    elif d == 0xf14:
        return Csr_index.mhartid
    elif d == 0x300:
        return Csr_index.mstatus
    elif d == 0x301:
        return Csr_index.misa
    elif d == 0x302:
        return Csr_index.medeleg
    elif d == 0x303:
        return Csr_index.mideleg
    elif d == 0x304:
        return Csr_index.mie
    elif d == 0x305:
        return Csr_index.mtvec
    elif d == 0x306:
        return Csr_index.mcounteren
    elif d == 0x340:
        return Csr_index.mscratch
    elif d == 0x341:
        return Csr_index.mepc
    elif d == 0x342:
        return Csr_index.mcause
    elif d == 0x343:
        return Csr_index.mtval
    elif d == 0x344:
        return Csr_index.mip
    elif d == 0x3a0:
        return Csr_index.pmpcfg0
    elif d == 0x3a1:
        return Csr_index.pmpcfg1
    elif d == 0x3a2:
        return Csr_index.pmpcfg2
    elif d == 0x3a3:
        return Csr_index.pmpcfg3
    elif d == 0x3b0:
        return Csr_index.pmpaddr0
    elif d == 0x3b1:
        return Csr_index.pmpaddr1
    elif d == 0x3b2:
        return Csr_index.pmpaddr2
    elif d == 0x3b3:
        return Csr_index.pmpaddr3
    elif d == 0x3b4:
        return Csr_index.pmpaddr4
    elif d == 0x3b5:
        return Csr_index.pmpaddr5
    elif d == 0x3b6:
        return Csr_index.pmpaddr6
    elif d == 0x3b7:
        return Csr_index.pmpaddr7
    elif d == 0x3b8:
        return Csr_index.pmpaddr8
    elif d == 0x3b9:
        return Csr_index.pmpaddr9
    elif d == 0x3ba:
        return Csr_index.pmpaddr10
    elif d == 0x3bb:
        return Csr_index.pmpaddr11
    elif d == 0x3bc:
        return Csr_index.pmpaddr12
    elif d == 0x3bd:
        return Csr_index.pmpaddr13
    elif d == 0x3be:
        return Csr_index.pmpaddr14
    elif d == 0x3bf:
        return Csr_index.pmpaddr15
    
    elif d == 0xb00:
        return Csr_index.mcycle
    elif d == 0xb02:
        return Csr_index.minstret
    elif d == 0x320:
        return Csr_index.mcountinhibit
    elif d == 0x323:
        return Csr_index.mhpevent3
    
    elif d == 0x7a0:
        return Csr_index.tselect
    elif d == 0x7a1:
        return Csr_index.tdata1
    elif d == 0x7a2:
        return Csr_index.tdata2
    elif d == 0x7a3:
        return Csr_index.tdata3
    
    elif d == 0x7b0:
        return Csr_index.dcsr
    elif d == 0x7b1:
        return Csr_index.dpc
    elif d == 0x7b2:
        return Csr_index.dscratch0
    elif d == 0x7b3:
        return Csr_index.dscratch1
    else:
        return Csr_index.invalid
    
csr = dict()
for index in Csr_index:
    csr[index] = 0


# In[ ]:


MSTATUS_SD_MSB = 63
MSTATUS_SD_LSB = 63
MSTATUS_SXL_MSB = 35
MSTATUS_SXL_LSB = 34
MSTATUS_UXL_MSB = 33
MSTATUS_UXL_LSB = 32
MSTATUS_TSR_MSB = 22
MSTATUS_TSR_LSB = 22
MSTATUS_TW_MSB = 21
MSTATUS_TW_LSB = 21
MSTATUS_TVM_MSB = 20
MSTATUS_TVM_LSB = 20
MSTATUS_MXR_MSB = 19
MSTATUS_MXR_LSB = 19
MSTATUS_SUM_MSB = 18
MSTATUS_SUM_LSB = 18
MSTATUS_MPRV_MSB = 17
MSTATUS_MPRV_LSB = 17
MSTATUS_XS_MSB = 16
MSTATUS_XS_LSB = 15
MSTATUS_FS_MSB = 14
MSTATUS_FS_LSB = 13
MSTATUS_MPP_MSB = 12
MSTATUS_MPP_LSB = 11
MSTATUS_SPP_MSB = 8
MSTATUS_SPP_LSB = 8
MSTATUS_MPIE_MSB = 7
MSTATUS_MPIE_LSB = 7
MSTATUS_SPIE_MSB = 5
MSTATUS_SPIE_LSB = 5
MSTATUS_UPIE_MSB = 4
MSTATUS_UPIE_LSB = 4
MSTATUS_MIE_MSB = 3
MSTATUS_MIE_LSB = 3
MSTATUS_SIE_MSB = 1
MSTATUS_SIE_LSB = 1
MSTATUS_UIE_MSB = 0
MSTATUS_UIE_LSB = 0

MIP_MEIP_MSB = 11
MIP_MEIP_LSB = 11
MIP_SEIP_MSB = 9
MIP_SEIP_LSB = 9
MIP_UEIP_MSB = 8
MIP_UEIP_LSB = 8
MIP_MTIP_MSB = 7
MIP_MTIP_LSB = 7
MIP_STIP_MSB = 5
MIP_STIP_LSB = 5
MIP_UTIP_MSB = 4
MIP_UTIP_LSB = 4
MIP_MSIP_MSB = 3
MIP_MSIP_LSB = 3
MIP_SSIP_MSB = 1
MIP_SSIP_LSB = 1
MIP_USIP_MSB = 0
MIP_USIP_LSB = 0

MIE_MEIE_MSB = 11
MIE_MEIE_LSB = 11
MIE_SEIE_MSB = 9
MIE_SEIE_LSB = 9
MIE_UEIE_MSB = 8
MIE_UEIE_LSB = 8
MIE_MTIE_MSB = 7
MIE_MTIE_LSB = 7
MIE_STIE_MSB = 5
MIE_STIE_LSB = 5
MIE_UTIE_MSB = 4
MIE_UTIE_LSB = 4
MIE_MSIE_MSB = 3
MIE_MSIE_LSB = 3
MIE_SSIE_MSB = 1
MIE_SSIE_LSB = 1
MIE_USIE_MSB = 0
MIE_USIE_LSB = 0






# In[6]:


LEVELS = 3
PTESIZE = 8
PAGESIZE = 1<<12 
def translate_addr(va,accesstype):
    return va


# In[67]:


def rtype(code):
    rd = fromto(code,11,7)
    rs1 = fromto(code,19,15)
    rs2 = fromto(code,24,20)
    return rd,rs1,rs2
def itype(code):
    rd = fromto(code,11,7)
    rs1 = fromto(code,19,15)
    imm = fromto(code,31,20)
    return rd,rs1,imm
def stype(code):
    rs1 = fromto(code,19,15)
    rs2 = fromto(code,24,20)
    imm = (fromto(code,31,25) << 5) | fromto(code,11,7)
    return rs1,rs2,imm
def btype(code):
    rs1 = fromto(code,19,15)
    rs2 = fromto(code,24,20)
    imm = (1<<11)*at(code,31)|(1<<10)*at(code,7)|16*fromto(code,30,25)|fromto(code,11,8)
    return rs1,rs2,imm
def utype(code):
    rd = fromto(code,11,7)
    imm = fromto(code,31,12)
    return rd,imm
def jtype(code):
    rd = fromto(code,11,7)
    imm = (1<<19)*at(code,31)|(1<<11)*fromto(code,19,12)|(1<<10)*at(code,20)|fromto(code,30,21)
    return rd,imm


# # RV32I

# In[2]:


def _addi(code):
    rd,rs1,imm = itype(code)
    write_reg(rd,unsigned((reg[rs1] + signed(imm,12)),64) % MAX_64)
def _slti(code):
    rd,rs1,imm = itype(code)
    if signed(reg[rs1],64) < signed(imm,12):
        write_reg(rd,1)
    else:
        write_reg(rd,0)
def _sltiu(code):
    rd,rs1,imm = itype(code)
    if reg[rs1] < extend(imm,12,64):
        write_reg(rd,1)
    else:
        write_reg(rd,0)
def _andi(code):
    rd,rs1,imm = itype(code)
    write_reg(rd,reg[rs1] & extend(imm,12,64))
def _ori(code):
    rd,rs1,imm = itype(code)
    write_reg(rd,reg[rs1] | extend(imm,12,64))
def _xori(code):
    rd,rs1,imm = itype(code)
    write_reg(rd,reg[rs1] ^ extend(imm,12,64))
#used in RV64I
#def _slli(code):
#    rd,rs1,imm = itype(code)
#    imm = fromto(imm,4,0)
#    reg[rd] = (reg[rs1] << imm) % MAX
#def _srli(code):
#    rd,rs1,imm = itype(code)
#    imm = fromto(imm,4,0)
#    reg[rd] = (reg[rs1] >> imm) % MAX
#def _srai(code):
#    rd,rs1,imm = itype(code)
#    imm = fromto(imm,4,0)
#    if reg[rs1] & (1<<63) > 0:
#        reg[rd] = (reg[rs1] >> imm)|(((1<<imm)-1)<<(64-imm)) % MAX
#    else:
#        reg[rd] = (reg[rs1] >> imm) % MAX
#def _lui(code):
#    rd,imm = utype(code)
#    reg[rd] = imm << 12
#def _auipc(code):
#    rd,imm = utype(code)
#    reg[rd] = (pc+imm<<12) % MAX_64
def _add(code):
    rd,rs1,rs2 = rtype(code)
    write_reg(rd,(reg[rs1]+reg[rs2]) % MAX_64)
def _slt(code):
    rd,rs1,rs2 = rtype(code)
    if signed(reg[rs1],64) < signed(reg[rs2],64):
        write_reg(rd,1)
    else:
        write_reg(rd,0)
def _sltu(code):
    rd,rs1,rs2 = rtype(code)
    if reg[rs1] < reg[rs2]:
        write_reg(rd,1)
    else:
        write_reg(rd,0)
def _and(code):
    rd,rs1,rs2 = rtype(code)
    write_reg(rd,reg[rs1] & reg[rs2])
def _or(code):
    rd,rs1,rs2 = rtype(code)
    write_reg(rd,reg[rs1] | reg[rs2])
def _xor(code):
    rd,rs1,rs2 = rtype(code)
    write_reg(rd,reg[rs1] ^ reg[rs2])
#def _sll(code):
#    rd,rs1,rs2 = rtype(code)
#    samt = fromto(reg[rs2],4,0)
#    write_reg(rd,(reg[rs1] << samt) % MAX_64)
#def _srl(code):
#    rd,rs1,rs2 = rtype(code)
#    samt = fromto(reg[rs2],4,0)
#    write_reg(rd,(reg[rs1] >> samt) % MAX_64)
def _sub(code):
    rd,rs1,rs2 = rtype(code)
    write_reg(rd,unsigned(reg[rs1]-reg[rs2],64))
#def _sra(code):
#    rd,rs1,rs2 = rtype(code)
#    imm = fromto(reg[rs2],4,0)
#    if reg[rs1] & (1<<63) > 0:
#        write_reg(rd,(reg[rs1] >> imm)|(((1<<imm)-1)<<(64-imm)) % MAX_64)
#    else:
#        write_reg(rd,(reg[rs1] >> imm) % MAX_64)
def _jal(code):
    rd,imm = jtype(code)
    write_reg(rd,pc+4)
    update_pc(pc + 2 * signed(imm,20))
def _jalr(code):
    rd,rs1,imm = itype(code)
    t = pc + 4
    u = unsigned(reg[rs1]+signed(imm,12),64)
    update_pc(u - (u&1))
    write_reg(rd,t)
def _beq(code):
    rs1,rs2,imm = btype(code)
    if reg[rs1] == reg[rs2]:
        update_pc(pc + 2 * signed(imm,12))
def _bne(code):
    rs1,rs2,imm = btype(code)
    if reg[rs1] != reg[rs2]:
        update_pc(pc + 2 * signed(imm,12))
def _blt(code):
    rs1,rs2,imm = btype(code)
    if signed(reg[rs1],64) < signed(reg[rs2],64):
        update_pc(pc + 2 * signed(imm,12))
def _bltu(code):
    rs1,rs2,imm = btype(code)
    if reg[rs1] < reg[rs2]:
        update_pc(pc + 2 * signed(imm,12))
def _bge(code):
    rs1,rs2,imm = btype(code)
    if signed(reg[rs1],64) >= signed(reg[rs2],64):
        update_pc(pc + 2 * signed(imm,12))
def _bgeu(code):
    rs1,rs2,imm = btype(code)
    if reg[rs1] >= reg[rs2]:
        update_pc(pc + 2 * signed(imm,12))
def _fence(code):
    return


# # RV64I

# In[ ]:


def _slli(code):
    rd,rs1,imm = itype(code)
    imm = fromto(imm,5,0)
    write_reg(rd,(reg[rs1] << imm) % MAX_64)
def _srli(code):
    rd,rs1,imm = itype(code)
    imm = fromto(imm,5,0)
    write_reg(rd,(reg[rs1] >> imm) % MAX_64)
def _srai(code):
    rd,rs1,imm = itype(code)
    imm = fromto(imm,5,0)
    if reg[rs1] & (1<<63) > 0:
        write_reg(rd,(reg[rs1] >> imm)|(((1<<imm)-1)<<(64-imm)) % MAX_64)
    else:
        write_reg(rd,(reg[rs1] >> imm) % MAX_64)
def _addiw(code):
    rd,rs1,imm = itype(code)
    write_reg(rd,extend(fromto(unsigned(signed(reg[rs1],64)+signed(imm,12),64) ,31,0),32,64) )
def _slliw(code):
    rd,rs1,imm = itype(code)
    imm = fromto(imm,4,0)
    write_reg(rd, extend(fromto(reg[rs1] << imm,31,0),32,64))
def _srliw(code):
    rd,rs1,imm = itype(code)
    imm = fromto(imm,4,0)
    write_reg(rd,extend(fromto(reg[rs1],31,0)>>imm,32,64))
def _sraiw(code):
    rd,rs1,imm = itype(code)
    imm = fromto(imm,4,0)
    base = fromto(reg[rs1],31,0)
    tmp = 0
    if base & (1<<31) > 0:
        tmp = (base >> imm)|(((1<<imm)-1)<<(32-imm))
    else:
        tmp = (base >> imm)
    write_reg(rd,extend(tmp,32,64))

def _lui(code):
    rd,imm = utype(code)
    write_reg(rd,extend(imm << 12,32,64))
def _auipc(code):
    rd,imm = utype(code)
    write_reg(rd,unsigned(pc+extend(imm<<12,32,64) ,64))
def _sll(code):
    rd,rs1,rs2 = rtype(code)
    samt = fromto(reg[rs2],5,0)
    write_reg(rd,(reg[rs1] << samt) % MAX_64)
def _srl(code):
    rd,rs1,rs2 = rtype(code)
    samt = fromto(reg[rs2],5,0)
    write_reg(rd,(reg[rs1] >> samt) % MAX_64)
def _sra(code):
    rd,rs1,rs2 = rtype(code)
    imm = fromto(reg[rs2],5,0)
    if reg[rs1] & (1<<63) > 0:
        write_reg(rd,(reg[rs1] >> imm)|(((1<<imm)-1)<<(64-imm)) % MAX_64)
    else:
        write_reg(rd,(reg[rs1] >> imm) % MAX_64)
def _addw(code):
    rd,rs1,rs2 = rtype(code)
    res = extend((fromto(reg[rs1],31,0)+fromto(reg[rs2],31,0))%MAX_32,32,64)
    write_reg(rd,res)
def _subw(code):
    rd,rs1,rs2 = rtype(code)
    res = extend(unsigned(fromto(reg[rs1],31,0)-fromto(reg[rs2],31,0),64)%MAX_32,32,64)
    write_reg(rd,res) 
def _sllw(code):
    rd,rs1,rs2 = rtype(code)
    imm = fromto(reg[rs2],4,0)
    write_reg(rd, extend(fromto(reg[rs1]<<imm,31,0),32,64))
def _srlw(code):
    rd,rs1,rs2 = rtype(code)
    imm = fromto(reg[rs2],4,0)
    write_reg(rd,extend(fromto(reg[rs1],31,0)>>imm,32,64))
def _sraw(code):
    rd,rs1,rs2 = rtype(code)
    imm = fromto(reg[rs2],4,0)
    base = fromto(reg[rs1],31,0)
    tmp = 0
    if base & (1<<31) > 0:
        tmp = (base >> imm)|(((1<<imm)-1)<<(32-imm))
    else:
        tmp = (base >> imm)
    write_reg(rd,extend(tmp,32,64))


# # Zifencei&Zicsr

# In[ ]:


#fence.iが実行されるとローカルな命令キャッシュと命令パイプラインがフラッシュされる(シンプルな実装では)
#フェッチパイプラインだけｆラッシュすればよい
def _fence_i(code):
    return
def _csrrw(code):
    rd,rs1,imm = itype(code)
    idx = get_csr_index(imm)
    write_reg(rd,csr[idx])
    csr[idx] = reg[rs1]
def _csrrs(code):
    rd,rs1,imm = itype(code)
    idx = get_csr_index(imm)
    write_reg(rd,csr[idx])
    if rs1 != 0:
        csr[idx] = csr[idx] | reg[rs1]
def _csrrc(code):
    rd,rs1,imm = itype(code)
    idx = get_csr_index(imm)
    write_reg(rd,csr[idx])
    if rs1 != 0:
        csr[idx] = csr[idx] & (~reg[rs1])
def _csrrwi(code):
    rd,uimm,imm = itype(code)
    idx = get_csr_index(imm)
    write_reg(rd,csr[idx])
    csr[idx] = uimm
def _csrrsi(code):
    rd,uimm,imm = itype(code)
    idx = get_csr_index(imm)
    write_reg(rd,csr[idx])
    if uimm != 0:
        csr[idx] = csr[idx] | uimm
def _csrrci(code):
    rd,uimm,imm = itype(code)
    idx = get_csr_index(imm)
    write_reg(rd,csr[idx])
    if uimm != 0:
        csr[idx] = csr[idx] & (~uimm)


# # Supervisor Instruction

# In[16]:


def sfence_vma(code):
    return


# # Priviledged Instruction

# In[ ]:


def _ecall(code):
    if mode == Mode.M:
        generate_exception(code,Exception.environment_call_from_mmode)
    elif mode == Mode.S:
        generate_exception(code,Exception.environment_call_from_smode)
    elif mode == Mode.U:
        generate_exception(code,Exception.environment_call_from_umode)
def _ebreak(code):
    generate_exception(code,Exception.breakpoint)
def _mret(code):
    global mode
    update_pc(csr[Csr_index.mepc])
    y = fromto(csr[Csr_index.mstatus],MSTATUS_MPP_MSB,MSTATUS_MPP_LSB)
    if y == 0b00:
        mode = Mode.U
    elif y == 0b01:
        mode = Mode.S
    else:
        mode = Mode.M
    write_csr(Csr_index.mstatus,MSTATUS_MIE_MSB,MSTATUS_MIE_LSB,
              fromto(csr[Csr_index.mstatus],MSTATUS_MPIE_MSB,MSTATUS_MPIE_LSB))
    write_csr(Csr_index.mstatus,MSTATUS_MPIE_MSB,MSTATUS_MPIE_LSB,1)
    write_csr(Csr_index.mstatus,MSTATUS_MPP_MSB,MSTATUS_MPP_LSB,0b00)

def _sret(code):
    global mode
    if mode == Mode.M:
        _mret(code)

    update_pc(csr[Csr_index.sepc])
    y = fromto(csr[Csr_index.mstatus],MSTATUS_SPP_MSB,MSTATUS_SPP_LSB)
    if y == 0b0:
        mode = Mode.U
    else:
        mode = Mode.S
    write_csr(Csr_index.mstatus,MSTATUS_SIE_MSB,MSTATUS_SIE_LSB,
              fromto(csr[Csr_index.mstatus],MSTATUS_SPIE_MSB,MSTATUS_SPIE_LSB))
    write_csr(Csr_index.mstatus,MSTATUS_SPIE_MSB,MSTATUS_SPIE_LSB,1)
    write_csr(Csr_index.mstatus,MSTATUS_SPP_MSB,MSTATUS_SPP_LSB,0b00)

def _uret(code):
    global mode
    if mode != Mode.U:
        _sret(code)
    update_pc(csr[Csr_index.uepc])
    y = fromto(csr[Csr_index.mstatus],MSTATUS_SPP_MSB,MSTATUS_SPP_LSB)
    if y == 0b00:
        mode = Mode.U
    elif y == 0b01:
        mode = Mode.S
    else:
        mode = Mode.M
    write_csr(Csr_index.mstatus,MSTATUS_UIE_MSB,MSTATUS_UIE_LSB,
              fromto(csr[Csr_index.mstatus],MSTATUS_UPIE_MSB,MSTATUS_UPIE_LSB))
    write_csr(Csr_index.mstatus,MSTATUS_UPIE_MSB,MSTATUS_UPIE_LSB,1)

def _wfi(code):
    return

def generate_exception(code,exception_code):
    global mode, pc
    if exception_code == Exception.environment_call_from_mmode:
        print("mcall ex.")
        tmp = csr[Csr_index.mepc]
        csr[Csr_index.mepc] = pc
    elif exception_code == Exception.environment_call_from_smode:
        print("scall ex.")
        csr[Csr_index.sepc] = pc
        mode = Mode.M
    elif exception_code == Exception.environment_call_from_umode:
        print("ucall ex.")
        csr[Csr_index.uepc] = pc
        mode = Mode.M
    elif exception_code == Exception.breakpoint:
        print("breakpoint ex.") 
    elif exception_code == Exception.illegal_instruction:
        print("illegal inst ex.")
    else:
        print("unknown ex.")
    if mode == Mode.M:
        csr[Csr_index.mcause] = int(exception_code)
    elif mode == Mode.S:
        csr[Csr_index.scause] = int(exception_code)
    elif mode == Mode.U:
        csr[Csr_index.ucause] = int(exception_code)
    update_pc(csr[Csr_index.mtvec])




# # Decoder

# In[ ]:


OPCODE_LOAD      = 0b0000011
OPCODE_STORE     = 0b0100011
OPCODE_MADD      = 0b1000011
OPCODE_BRANCH    = 0b1100011
OPCODE_LOAD_FP   = 0b0000111
OPCODE_STORE_FP  = 0b0100111
OPCODE_MSUB      = 0b1000111
OPCODE_JALR      = 0b1100111
OPCODE_NMSUB     = 0b1001011
OPCODE_MISC_MEM  = 0b0001111
OPCODE_AMO       = 0b0101111
OPCODE_NMADD     = 0b1001111
OPCODE_JAL       = 0b1101111
OPCODE_OP_IMM    = 0b0010011
OPCODE_OP        = 0b0110011
OPCODE_OP_FP     = 0b1010011
OPCODE_SYSTEM    = 0b1110011
OPCODE_AUPIC     = 0b0010111
OPCODE_LUI       = 0b0110111
OPCODE_OP_IMM_32 = 0b0011011
OPCODE_OP_32     = 0b0111011

def decode(inst):
    opcode = fromto(inst,6,0)
    funct3 = fromto(inst,14,12)
    funct7 = fromto(inst,31,25)
    if   opcode == OPCODE_LUI:
        _lui(inst)
    elif opcode == OPCODE_AUPIC:
        _auipc(inst)
    elif opcode == OPCODE_JAL:
        _jal(inst)
    elif opcode == OPCODE_JALR:
        _jalr(inst)
    elif opcode == OPCODE_BRANCH:
        if   funct3 == 0b000:
            _beq(inst)
        elif funct3 == 0b001:
            _bne(inst)
        elif funct3 == 0b100:
            _blt(inst)
        elif funct3 == 0b101:
            _bge(inst)
        elif funct3 == 0b110:
            _bltu(inst)
        elif funct3 == 0b111:
            _bgeu(inst)
        else:
            generate_exception(inst,Exception.illegal_instruction)
    elif opcode == OPCODE_LOAD:
        if   funct3 == 0b000:
            _lb(inst)
        elif funct3 == 0b001:
            _lh(inst)
        elif funct3 == 0b010:
            _lw(inst)
        elif funct3 == 0b011:
            _ld(inst)
        elif funct3 == 0b100:
            _lbu(inst)
        elif funct3 == 0b101:
            _lhu(inst)
        elif funct3 == 0b110:
            _lwu(inst)
        else:
            generate_exception(inst,Exception.illegal_instruction)
    elif opcode == OPCODE_STORE:
        if   funct3 == 0b000:
            _sb(inst)
        elif funct3 == 0b001:
            _sh(inst)
        elif funct3 == 0b010:
            _sw(inst)
        elif funct3 == 0b011:
            _sd(inst)
        else:
            generate_exception(inst,Exception.illegal_instruction)
    elif opcode == OPCODE_OP_IMM:
        if   funct3 == 0b000:
            print("addi",inst)
            _addi(inst)
        elif funct3 == 0b010:
            _slti(inst)
        elif funct3 == 0b011:
            _sltiu(inst)
        elif funct3 == 0b100:
            _xori(inst)
        elif funct3 == 0b110:
            _ori(inst)
        elif funct3 == 0b111:
            _andi(inst)
        elif funct3 == 0b001:
            _slli(inst)
        elif funct3 == 0b101:
            if   funct7 == 0:
                _srli(inst)
            elif funct7 == 0b100000:
                _srai(inst)
            else:
                generate_exception(inst,Exception.illegal_instruction)
        else:
            generate_exception(inst,Exception.illegal_instruction)
    elif opcode == OPCODE_OP:
        #RV32/64M here
        
        
        if   funct3 == 0b000:
            if   funct7 == 0:
                _add(inst)
            elif funct7 == 0b100000:
                _sub(inst)
            else:
                generate_exception(inst,Exception.illegal_instruction)
        elif funct3 == 0b001:
            _sll(inst)
        elif funct3 == 0b010:
            _slt(inst)
        elif funct3 == 0b011:
            _sltu(inst)
        elif funct3 == 0b100:
            _xor(inst)
        elif funct3 == 0b101:
            if   funct7 == 0:
                _srl(inst)
            elif funct7 == 0b100000:
                _sra(inst)
            else:
                generate_exception(inst,Exception.illegal_instruction)
        elif funct3 == 0b110:
            _or(inst)
        elif funct3 == 0b111:
            _and(inst)
        else:
            generate_exception(inst,Exception.illegal_instruction)
    elif opcode == OPCODE_MISC_MEM:
        if   funct3 == 0b000:
            _fence(inst)
        elif funct3 == 0b001:
            _fence_i(inst)
        else:
            generate_exception(inst,Exception.illegal_instruction)
    elif opcode == OPCODE_SYSTEM:
        if   funct3 == 0b000:
            if fromto(inst,24,20) == 0b00010:
                if funct7 == 0:
                    _uret(inst)
                elif funct7 == 0b1000:
                    _sret(inst)
                elif funct7 == 0b11000:
                    _mret(inst)
                else:
                    generate_exception(inst,Exception.illegal_instruction)
            elif funct7 == 0:
                _ecall(inst)
            elif funct7 == 1:
                _ebreak(inst)
            else:
                generate_exception(inst,Exception.illegal_instruction)
        elif get_csr_index(fromto(inst,31,20)) not in csr:
            generate_exception(inst,Exception.illegal_instruction)
        elif funct3 == 0b001:
            _csrrw(inst)
        elif funct3 == 0b010:
            _csrrs(inst)
        elif funct3 == 0b011:
            _csrrc(inst)
        elif funct3 == 0b101:
            _csrrwi(inst)
        elif funct3 == 0b110:
            _csrrsi(inst)
        elif funct3 == 0b111:
            _csrrci(inst)
        else:
            generate_exception(inst,Exception.illegal_instruction)
    elif opcode == OPCODE_OP_IMM_32:
        if   funct3 == 0b000:
            _addiw(inst)
        elif funct3 == 0b001:
            _slliw(inst)
        elif funct3 == 0b101:
            if funct7 == 0:
                _srliw(inst)
            elif funct7 == 0b100000:
                _sraiw(inst)
            else:
                generate_exception(inst,Exception.illegal_instruction)
        else:
            generate_exception(inst,Exception.illegal_instruction)   
    elif opcode == OPCODE_OP_32:
        if funct3 == 0b000:
            if funct7 == 0:
                _addw(inst)
            elif funct7 == 0b100000:
                _subw(inst)
            else:
                generate_exception(inst,Exception.illegal_instruction)
        elif funct3 == 0b001:
            _sllw(inst)
        elif funct3 == 0b101:
            if funct7 == 0:
                _srlw(inst)
            elif funct7 == 0b100000:
                _sraw(inst)
            else:
                generate_exception(inst,Exception.illegal_instruction)
        else:
            generate_exception(inst,Exception.illegal_instruction)
    else:
        generate_exception(inst,Exception.illegal_instruction)
    global pc_updated
    if pc_updated == False:
        update_pc(pc+4)
    pc_updated = False


# In[7]:


def reset():
    csr[Csr_index.misa] = 0x8000000000000000 | 0b000000101000001000101101001
    csr[Csr_index.mtvec] = ADDR_BASE 
    csr[Csr_index.mcause] = 0
    csr[Csr_index.mvendorid] = 0
    csr[Csr_index.marchid] = 0
    csr[Csr_index.mhartid] = 0
    global pc, mode, finished, pc_updated
    pc = ADDR_FROMHOST
    mode = Mode.M
    finished = False
    pc_updated = False
    
def fetch():
    va = translate_addr(pc,MemoryAccessType.instruction)
    print(hex(va))
    print(hex(load_word(va)))
    return load_word(va)


# In[ ]:


import struct
def emulate(filename):
    global finished
    tmp = ADDR_BASE
    with open(filename,mode="rb") as f:
        data = f.read()
        for i in range(len(data)):
            store_byte(tmp,data[i])
            tmp += 1
    reset()
    for i in range(2**16):
        if finished:
            print("program terminated.")
            break
        inst = fetch()
        decode(inst)
    else:
        print("program not terminated in limited cycles")
            


# In[ ]:


import sys
if __name__=="__main__":
    args = sys.argv
    emulate(args[1])
    if tohost_data == 1:
        print("PASS: ",args[1])
    else:
        print("FAIL: ",args[1])


