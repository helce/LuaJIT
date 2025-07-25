/*
** Definitions for E2K CPUs.
** Copyright (C) 2005-2021 Mike Pall. See Copyright Notice in luajit.h
*/

#ifndef _LJ_TARGET_E2K_H
#define _LJ_TARGET_E2K_H

/* -- Registers IDs ------------------------------------------------------- */

#define GPRDEF(_) \
   _(R0)  _(R1)  _(R2)  _(R3)  _(R4)  _(R5)  _(R6)  _(R7)   _(R8)  _(R9) \
  _(R10) _(R11) _(R12) _(R13) _(R14) _(R15) _(R16) _(R17)  _(R18) _(R19) \
  _(R20) _(R21) _(R22) _(R23) _(R24) _(R25) _(R26) _(R27)  _(R28) _(R29) \
  _(R30) _(R31)
/* _(R32) _(R33) _(R34) _(R35) _(R36) _(R37)  _(R38) _(R39) \
  _(R40) _(R41) _(R42) _(R43) _(R44) _(R45) _(R46) _(R47)  _(R48) _(R49) \
  _(R50) _(R51) _(R52) _(R53) _(R54) _(R55) _(R56) _(R57)  _(R58) _(R59) \
  _(R60) _(R61) _(R62) _(R63) */

#define FPRDEF(_)

#define BREGDEF(_) \
   _(B0)  _(B1)  _(B2)  _(B3)  _(B4)  _(B5)  _(B6)  _(B7)
/*   _(B8)  _(B9) \
  _(B10) _(B11) _(B12) _(B13) _(B14) _(B15) _(B16) _(B17) _(B18) _(B19) \
  _(B20) _(B21) _(B22) _(B23) _(B24) _(B25) _(B26) _(B27) _(B28) _(B29) \
  _(B30) _(B31) _(B32) _(B33) _(B34) _(B35) _(B36) _(B37) _(B38) _(B39) */
/* Interpreter uses only b0-b35
  _(B40) _(B41) _(B42) _(B43) _(B44) _(B45) _(B46) _(B47) _(B48) _(B49) \
  _(B50) _(B51) _(B52) _(B53) _(B54) _(B55) _(B56) _(B57) _(B58) _(B59) \
  _(B60) _(B61) _(B62) _(B63) _(B64) _(B65) _(B66) _(B67) _(B68) _(B69) \
  _(B70) _(B71) _(B72) _(B73) _(B74) _(B75) _(B76) _(B77) _(B78) _(B79) \
  _(B80) _(B81) _(B82) _(B83) _(B84) _(B85) _(B86) _(B87) _(B88) _(B89) \
  _(B90) _(B91) _(B92) _(B93) _(B94) _(B95) _(B96) _(B97) _(B98) _(B99) \
  _(B100) _(B101) _(B102) _(B103) _(B104) _(B105) _(B106) _(B107) _(B108) \
  _(B109) _(B110) _(B111) _(B112) _(B113) _(B114) _(B115) _(B116) _(B117) \
  _(B118) _(B119) _(B120) _(B121) _(B122) _(B123) _(B124) _(B125) _(B126) \
  _(B127) */

/*
   _(G0)  _(G1)  _(G2)  _(G3)  _(G4)  _(G5)  _(G6)  _(G7)  _(G8)  _(G9) \
  _(G10) _(G11) _(G12) _(G13) _(G14) _(G15)
*/

#define GREGDEF(_) \
  _(G16) _(G17) _(G18) _(G19) \
  _(G20) _(G21) _(G22) _(G23) _(G24) _(G25) _(G26) _(G27) _(G28) _(G29) \
  _(G30) _(G31)

#define PREDREGDEF(_) \
   _(PRED0)  _(PRED1)  _(PRED2)  _(PRED3)
/*  _(PRED4)  _(PRED5)  _(PRED6) \
   _(PRED7)  _(PRED8)  _(PRED9) _(PRED10) _(PRED11) _(PRED12) _(PRED13) \
  _(PRED14) _(PRED15) _(PRED16) _(PRED17) _(PRED18) _(PRED19) _(PRED20) \
  _(PRED21) _(PRED22) _(PRED23) _(PRED24) _(PRED25) _(PRED26) _(PRED27) \
  _(PRED28) _(PRED29) _(PRED30) _(PRED31) */

#define CTPRDEF(_) \
  _(CTPR1) _(CTPR2) _(CTPR3)

#define VRIDDEF(_)

#define RIDENUM(name) RID_##name,

enum {
  GPRDEF(RIDENUM)  /* Directly addressable registers of the current window */
  BREGDEF(RIDENUM)  /* Rotating registers of the current window */
  GREGDEF(RIDENUM)  /* Global registers */
  PREDREGDEF(RIDENUM) /* Predicates */
  CTPRDEF(RIDENUM) /* Control transer preparation registers */
  RID_MAX,
  RID_TMP = RID_G16,
  RID_BASE = RID_R4,  /* Interpreter BASE */
  RID_SP = RID_R6,  /* Interpreter stack pointer */
  RID_LPC = RID_R7, /* Interpreter PC */
  /* Calling conventions */
  /* TODO check is it return from or return to, cos in e2k they are different */
  RID_RETLO = RID_R0,
  RID_RETHI = RID_R1,
  RID_RET = RID_R0,
  RID_FPRET = RID_R0,

  RID_MIN_GPR = RID_R0,
  RID_MAX_GPR = RID_CTPR3+1,
  RID_MIN_FPR = 0,
  RID_MAX_FPR = RID_MIN_FPR,

  RID_NUM_GPR = RID_MAX_GPR - RID_MIN_GPR,
  RID_NUM_FPR = RID_MAX_FPR - RID_MIN_FPR
};

/* -- Register sets ------------------------------------------------------- */

/* Make use of all registers, except SP */
#define RSET_FIXED \
    (RID2RSET(RID_SP))
/* bitset, can be only 63 regs here, TODO check how much do we really need and which types */
#define RSET_GPR    (RSET_RANGE(RID_R0, RID_R31+1) - RSET_FIXED)
#define RSET_PRED   (RSET_RANGE(RID_PRED0, RID_PRED3+1))
#define RSET_CTPR   (RSET_RANGE(RID_CTPR1, RID_CTPR3+1))
#define RSET_FPR    0
#define RSET_ALL    (RSET_GPR|RSET_PRED|RSET_CTPR)
#define RSET_INIT   RSET_ALL


/* TODO check what do they mean of scratch */
#define RSET_SCRATCH_FPR  0
#define RSET_SCRATCH_GPR  0
#define RSET_SCRATCH    (RSET_SCRATCH_GPR|RSET_SCRATCH_FPR)

/* TODO wtf is regarg??? */
#define REGARG_NUMGPR   8

/* -- Spill slots --------------------------------------------------------- */

/* Spill slots are 32 bit wide.
**
** SPS_FIXED: Available fixed spill slots in interpreter frame.
** This definition must match with the *.dasc file(s).
**
** SPS_FIRST: First spill slot for general use.
*/
/* TODO no idea what is it */
#define SPS_FIXED 0
#define SPOFS_TMP 0
#define SPS_FIRST 0

/* TODO check about slots */
#define sps_scale(slot)   (4 * (int32_t)(slot))
/* TODO check is it align 16?? */
#define sps_align(slot)   (((slot) - SPS_FIXED + 1) & ~1)

/* -- Exit state ---------------------------------------------------------- */

/* This definition must match with the *.dasc file(s). */
typedef struct {
  intptr_t gpr[RID_NUM_GPR];
  int32_t spill[256];
} ExitState;


static LJ_AINLINE uint32_t *exitstub_trace_addr_(uint32_t *p, uint32_t exitno)
{
  __builtin_trap();
}

#define exitstub_trace_addr(T, exitno) \
  exitstub_trace_addr_((MCode *)((char *)(T)->mcode + (T)->szmcode), (exitno))

/* -- e2k bundle ---------------------------------------------------------- */

enum {
  /* HS */
  RES_ALS0    = 0x0001,
  RES_ALS1    = 0x0002,
  RES_ALS2    = 0x0004,
  RES_ALS3    = 0x0008,
  RES_ALS4    = 0x0010,
  RES_ALS5    = 0x0020,
  RES_CS0     = 0x0040,
  RES_CS1     = 0x0080,
  RES_AAS0    = 0x0100,
  RES_AAS1    = 0x0200,
  RES_AAS2    = 0x0400,
  RES_AAS3    = 0x0800,
  RES_AAS4    = 0x1000,
  RES_AAS5    = 0x2000,
  RES_LTS0    = 0x4000,
  RES_LTS1    = 0x8000,
  RES_LTS2    = 0x10000,
  RES_LTS3    = 0x20000,
  RES_PLS0    = 0x40000,
  RES_PLS1    = 0x80000,
  RES_PLS2    = 0x100000,
  RES_CDS0    = 0x200000,
  RES_CDS1    = 0x400000,
  RES_CDS2    = 0x800000,
  RES_ALES0   = 0x1000000,
  RES_ALES1   = 0x2000000,
  RES_ALES2   = 0x4000000,
  RES_ALES3   = 0x8000000,
  RES_ALES4   = 0x10000000,
  RES_ALES5   = 0x20000000,
  RES_SS      = 0x40000000,
  RES_MASK    = 0x7fffffff,
  RES_INIT    = RES_MASK,
  RES_NONE    = 0,
  RES_ALS_012345 = RES_ALS0 | RES_ALS1 | RES_ALS2 | RES_ALS3 | RES_ALS4 | RES_ALS5,
  RES_ALS_0134   = RES_ALS0 | RES_ALS1 | RES_ALS3 | RES_ALS4,
  RES_ALS_03     = RES_ALS0 | RES_ALS3,
  RES_ALS_25     = RES_ALS2 | RES_ALS5,
  RES_ALS_ALL    = RES_ALS_012345,
  RES_ALES_ALL   = RES_ALES0 | RES_ALES1 | RES_ALES2 | RES_ALES3 | RES_ALES4 | RES_ALES5,
  RES_CS_ALL     = RES_CS0 | RES_CS1,
  RES_LTS_ALL    = RES_LTS0 | RES_LTS1 | RES_LTS2| RES_LTS3,
  RES_ALES_SHIFT = 24,
  RES_CS_SHIFT   = 6,
  RES_LTS_SHIFT  = 14
};

typedef struct {
  uint8_t f1;
  uint8_t f2;
  uint8_t f3;
  uint8_t f4;
//  uint8_t hs_pls;
//  uint8_t hs_cds;
  uint32_t nop;
  uint32_t res;
  uint32_t ss;
  uint32_t als[6];
  uint32_t cs[2];
  uint16_t ales[6];
//  uint16_t aas[6];
  uint32_t lts[4];
//  uint32_t pls[3];
//  uint32_t cds[3];
} E2kBundle;

typedef struct {
  int type;
  union {
    uint8_t u4;
    uint8_t u5;
    uint16_t u16;
    uint32_t u32;
    uint64_t u64;
    uint32_t regn;
  } value;
} E2kOperand;

/* -- Instructions -------------------------------------------------------- */

typedef union {
  uint32_t i;
  struct {
    uint32_t mdl     : 4;
    uint32_t lng     : 3;
    uint32_t nop     : 3;
    uint32_t lm      : 1;
    uint32_t x_s_sw  : 3;
    uint32_t c       : 2;
    uint32_t cds     : 2;
    uint32_t pls     : 2;
    uint32_t ales    : 6;
    uint32_t als     : 6;
  } fields;
} E2kHS;

typedef union {
  uint32_t i;
  struct {
    uint32_t ctcond  : 9;
    uint32_t x       : 1;
    uint32_t ctop    : 2;
    uint32_t aa      : 4;
    uint32_t alc     : 2;
    uint32_t abp     : 2;
    uint32_t type    : 1;
    uint32_t abn     : 2;
    uint32_t abg     : 2;
    uint32_t rp_lo   : 1;
    uint32_t vfdi    : 1;
    uint32_t rp_hi   : 1;
    uint32_t bap     : 1;
    uint32_t eap     : 1;
    uint32_t ipd     : 2;
  } fields;
} E2kSS;

typedef union {
  uint32_t i;
  struct {
    uint32_t dst     : 8;
    uint32_t src2    : 8;
    uint32_t src1    : 8;
    uint32_t cop     : 7;
    uint32_t spec    : 1;
  } fields;
} E2kAlopf1;

typedef union {
  uint32_t i;
  struct {
    uint32_t src3    : 8;
    uint32_t src2    : 8;
    uint32_t src1    : 8;
    uint32_t cop     : 7;
    uint32_t spec    : 1;
  } fields;
} E2kAlopf3;

typedef union {
  uint32_t i;
  struct {
    uint32_t pdst    : 5;
    uint32_t cmpopce : 3;
    uint32_t src2    : 8;
    uint32_t src1    : 8;
    uint32_t cop     : 7;
    uint32_t spec    : 1;
  } fields;
} E2kAlopf7;

typedef union {
  uint32_t i;
  struct {
    uint32_t disp    : 28;
    uint32_t opc     : 2;
    uint32_t ctpr    : 2;
  } fields;
} E2kCopf2;

#define REG_R 1
#define REG_B 2
#define REG_G 3
#define REG_CTPR 65
#define CONST_U4 4
#define CONST_U5 5
#define CONST_U16 16
#define CONST_U32 32
#define CONST_U64 64

/* -- stack layout of interpreter. Must match with lj_frame.h ------------- */
#define E2K_STACK_TMP 0x68

/* -- Opcodes ------------------------------------------------------------- */

/* control operations */
#define OPC_DISP   0x0
/* non-combined operations short */
#define OPC_ADDS   0x10
#define OPC_ADDD   0x11
#define OPC_SUBS   0x12
#define OPC_SUBD   0x13
#define OPC_CMPSB  0x20
#define OPC_CMPDB  0x21
#define OPC_STW    0x26
#define OPC_FCMPDB 0x2f
#define OPC_FADDD  0x31
#define OPC_FSUBD  0x33
#define OPC_FMULD  0x39
/* non-combined operations long */
#define OPC_MULS   0x20
#define OPC_MULD   0x21
/* integer comparation opce */
#define CMPI_O     0x0
#define CMPI_B     0x1
#define CMPI_EQ    0x2
#define CMPI_BE    0x3
#define CMPI_S     0x4
#define CMPI_P     0x5
#define CMPI_LT    0x6
#define CMPI_LE    0x7
/* fp comporation opce */
#define CMPF_EQ    0x0
#define CMPF_LT    0x1
#define CMPF_LE    0x2
#define CMPF_UO    0x3
#define CMPF_NE    0x4
#define CMPF_NLT   0x5
#define CMPF_NLE   0x6
#define CMPF_OD    0x7

/* -- static latency ------------------------------------------------------ */
#define E2K_NOP_DISP_CT 4
#define E2K_NOP_OUT4F   3

#endif
