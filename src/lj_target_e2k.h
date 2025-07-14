/*
** Definitions for E2K CPUs.
** Copyright (C) 2005-2021 Mike Pall. See Copyright Notice in luajit.h
*/

#ifndef _LJ_TARGET_E2K_H
#define _LJ_TARGET_E2K_H

/* -- Registers IDs ------------------------------------------------------- */

#define RREGDEF(_) \
   _(R0)  _(R1)  _(R2)  _(R3)  _(R4)  _(R5)  _(R6)  _(R7)   _(R8)  _(R9) \
  _(R10) _(R11) _(R12) _(R13) _(R14) _(R15) _(R16) _(R17)  _(R18) _(R19) \
  _(R20) _(R21) _(R22) _(R23) _(R24) _(R25) _(R26) _(R27)  _(R28) _(R29) \
  _(R30) _(R31) _(R32) _(R33) _(R34) _(R35) _(R36) _(R37)  _(R38) _(R39) \
  _(R40) _(R41) _(R42) _(R43) _(R44) _(R45) _(R46) _(R47)  _(R48) _(R49) \
  _(R50) _(R51) _(R52) _(R53) _(R54) _(R55) _(R56) _(R57)  _(R58) _(R59) \
  _(R60) _(R61) _(R62) _(R63)

#define BREGDEF(_) \
   _(B0)  _(B1)  _(B2)  _(B3)  _(B4)  _(B5)  _(B6)  _(B7)   _(B8)  _(B9) \
  _(B10) _(B11) _(B12) _(B13) _(B14) _(B15) _(B16) _(B17) _(B18) _(B19) \
  _(B20) _(B21) _(B22) _(B23) _(B24) _(B25) _(B26) _(B27) _(B28) _(B29) \
  _(B30) _(B31) _(B32) _(B33) _(B34) _(B35) _(B36) _(B37) _(B38) _(B39)
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

#define GREGDEF(_) \
   _(G0)  _(G1)  _(G2)  _(G3)  _(G4)  _(G5)  _(G6)  _(G7)  _(G8)  _(G9) \
  _(G10) _(G11) _(G12) _(G13) _(G14) _(G15) _(G16) _(G17) _(G18) _(G19) \
  _(G20) _(G21) _(G22) _(G23) _(G24) _(G25) _(G26) _(G27) _(G28) _(G29) \
  _(G30) _(G31)

#define PREDREGDEF(_) \
   _(PRED0)  _(PRED1)  _(PRED2)  _(PRED3)  _(PRED4)  _(PRED5)  _(PRED6) \
   _(PRED7)  _(PRED8)  _(PRED9) _(PRED10) _(PRED11) _(PRED12) _(PRED13) \
  _(PRED14) _(PRED15) _(PRED16) _(PRED17) _(PRED18) _(PRED19) _(PRED20) \
  _(PRED21) _(PRED22) _(PRED23) _(PRED24) _(PRED25) _(PRED26) _(PRED27) \
  _(PRED28) _(PRED29) _(PRED30) _(PRED31)

#define CTPRREGDEF(_) \
  _(CTPR1) _(CTPR2) _(CTPR3)

#define RIDENUM(name) RID_##name,

enum {
  RREGDEF(RIDENUM)  /* Directly addressable registers of the current window */
  BREGDEF(RIDENUM)  /* Rotating registers of the current window */
  GREGDEF(RIDENUM)  /* Global registers */
  PREDREGDEF(RIDENUM) /* Predicates */
  CTPRREGDEF(RIDENUM) /* Control transer preparation registers */
  RID_MIN_GPR = RID_R0,
  RID_MAX_GPR = RID_CTPR3+1,

  RID_NUM_GPR = RID_MAX_GPR - RID_MIN_GPR
};

#endif
