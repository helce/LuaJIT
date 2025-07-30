/*
** E2K instruction emitter.
** Copyright (C) 2005-2025 Mike Pall. See Copyright Notice in luajit.h
*/

#define NIY __builtin_trap();

/* -- Bundling ------------------------------------------------------------ */

static uint32_t check_resource(ASMState *as, uint32_t mask)
{
  uint32_t res = as->bundle.res & mask;
  if (!res) {
    // TODO need to finalize first or just error.
    NIY
  }
  res = res & (-res);
  as->bundle.res &= ~res;
  return res;
}

#define UT(t) u##t
#define E2K_CONST(t, val, op) \
  op.type = t; \
  op.value.UT(t) = val;

#define E2K_REG(t, val, op) \
  op.type = t; \
  op.value.regn = val;

#define checku4(x)  ((x) == (int32_t)(uint8_t)(x & 0xf))
#define checku5(x)  ((x) == (int32_t)(uint8_t)(x & 0x1f))

static intptr_t get_kval(ASMState *as, IRRef ref)
{
  IRIns *ir = IR(ref);
  if (irt_is64(ir->t)) {
    return (intptr_t)ir_k64(ir)->u64;
  } else {
    lj_assertA(ir->o == IR_KINT || ir->o == IR_KNULL,
               "bad 64 bit const IR op %d", ir->o);
    return ir->i; /* Sign-extended. */
  }
}

static E2kOp get_reg_type(intptr_t val)
{
  if (val <= RID_R31)
    return E2K_REG_R;
  else if (val <= RID_B7)
    return E2K_REG_B;
  else if (val <= RID_G31)
    return E2K_REG_G;
  else if (val <= RID_PRED3)
    return E2K_REG_PRED;
  else if (val <= RID_CTPR3)
    return E2K_REG_CTPR;
  else
    return E2K_REG_UNKNOWN;
}

static E2kOp get_const_type(intptr_t val)
{
  if (checku4(val))
    return E2K_CONST4;
  else if(checku5(val))
    return E2K_CONST5;
  else if (checki16(val))
    return E2K_CONST16;
  else if (checki32(val))
    return E2K_CONST32;
  else
    return E2K_CONST64;
}

/* -- Bundle -------------------------------------------------------------- */

static void emit_bundle_setup(ASMState *as)
{
  memset(&as->bundle, 0, sizeof(E2kBundle));
  as->bundle.res = RES_INIT;
  as->bundle.f1 = 1; // HS itself
}

static MCode *emit_bundle_finalize(ASMState *as, MCode *mxp)
{
  uint8_t f1 = as->bundle.f1;
  uint8_t f2 = as->bundle.f2;
  int half_pad = as->bundle.f3 & 0x1;
  uint8_t f3 = (as->bundle.f3 >> 1) + half_pad;
  uint8_t f4 = as->bundle.f4;
  uint8_t lng = f1 + f2 + f3 + f4;
  uint8_t hs_lng = (lng + 1) & -2;

  E2kHS hs;
  hs.i = 0;
  hs.fields.mdl = (uint32_t)(f1 + f2 - 1);
  hs.fields.lng = (uint32_t)(hs_lng >> 1) - 1;
  hs.fields.nop = (uint32_t)as->bundle.nop;
//  hs.fields.lm = (uint32_t)as->bundle.loop;
  uint32_t hs_x_s_sw = (as->bundle.res & RES_SS) ? 0 : 0x2;
  hs.fields.x_s_sw = hs_x_s_sw;
  uint32_t hs_c = (~as->bundle.res & RES_CS_ALL) >> RES_CS_SHIFT;
  hs.fields.c = hs_c;
//  hs.fields.cds = (uint32_t)as->bundle.hs_cds;
//  hs.fields.pls = (uint32_t)as->bundle.hs_pls;
  uint32_t hs_ales = (~as->bundle.res & RES_ALES_ALL) >> RES_ALES_SHIFT;
  hs.fields.ales = hs_ales;
  uint32_t hs_als = ~as->bundle.res & RES_ALS_ALL;
  hs.fields.als = hs_als;

  // cds, 16-bit halfsyls, not used 
  // pls, 32-bit syls, not used
  int used_lts = ((~as->bundle.res & RES_LTS_ALL) >> RES_LTS_SHIFT);
  for (int i = 0; i < 4; i++) {
    if (used_lts & (1 << i)) {
      *--mxp = as->bundle.lts[i];
    }
  }
  if (hs_lng != lng) {
    *--mxp = 0;
  }
  // aas, 16-bit syls, not used
  uint16_t *hmxp = (uint16_t *)mxp;
  if (half_pad) *--hmxp = 0;
  if (hs_ales & 0x10) *--hmxp = as->bundle.ales[4];
  if (hs_ales & 0x08) *--hmxp = as->bundle.ales[3];
  if (hs_ales & 0x02) *--hmxp = as->bundle.ales[1];
  if (hs_ales & 0x01) *--hmxp = as->bundle.ales[0];
  mxp = (MCode *)hmxp;
  if (hs_c & 0x02) *--mxp = as->bundle.cs[1];
  if (hs_c & 0x01) *--mxp = (as->bundle.cs[0] + (hs_lng >> 1));
  if (hs_als & 0x20) *--mxp = as->bundle.als[5];
  if (hs_als & 0x10) *--mxp = as->bundle.als[4];
  if (hs_als & 0x08) *--mxp = as->bundle.als[3];
  if (hs_als & 0x04) *--mxp = as->bundle.als[2];
  if (hs_als & 0x02) *--mxp = as->bundle.als[1];
  if (hs_als & 0x01) *--mxp = as->bundle.als[0];
  if (hs_x_s_sw) *--mxp = as->bundle.ss;
  *--mxp = hs.i; 

  emit_bundle_setup(as);
  return mxp;
}

/* -- Emit basic instructions --------------------------------------------- */

static int emit_als(ASMState *as, uint32_t als_mask)
{
  uint32_t als = check_resource(as, als_mask);
  // convert to index
  int als_idx = 0;
  while (als >>= 1) {
    als_idx++;
  }
  return als_idx;
}

//TODO refactor
static uint32_t emit_lts(ASMState *as, E2kOp type, uint64_t val)
{
  uint32_t mask = 0;
  if (type == E2K_CONST16) {
    mask = RES_LTS1|RES_LTS0;
  } else if (type == E2K_CONST32) {
    mask = RES_LTS3|RES_LTS2|RES_LTS1|RES_LTS0;
  } else {
    mask = RES_LTS2|RES_LTS1|RES_LTS0;
  }
  // TODO, manage halfsyls, now just lo part.
  uint32_t lts = check_resource(as, mask);
  // takes two lts
  if (type == E2K_CONST64) {
    check_resource(as, lts << 1);
  }

  lts >>= 14;
  // convert to index
  int lts_idx = 0;
  while (lts >>= 1) {
    lts_idx++;
  }
  switch (type) {
  case E2K_CONST16:
    as->bundle.lts[lts_idx] = (uint16_t)(val); break;
  case E2K_CONST32:
    as->bundle.lts[lts_idx] = (uint32_t)(val); break;
  case E2K_CONST64:
    as->bundle.lts[lts_idx] = (uint32_t)(val);
    as->bundle.lts[lts_idx+1] = (uint32_t)(val >> 32);
    as->bundle.f4++;
    break;
  }
  as->bundle.f4++;
  return lts_idx;
}

static uint32_t emit_src1(ASMState *as, E2kOp type, intptr_t src1)
{
  UNUSED(as);
  if (type == E2K_REG) {
    switch (get_reg_type(src1)) {
    case E2K_REG_B:
      return src1 - RID_B0;
    case E2K_REG_R:
      return (src1 - RID_R0) | 0x80;
    case E2K_REG_G:
      return (src1 - RID_G16 + 16) | 0xe0;
    default:
      lj_assertA(0, "bad reg for src1 (%d)", src1);
      return 0;
    }
  } else {
    switch (get_const_type(src1)) {
    case E2K_CONST4: case E2K_CONST5:
      return src1 | 0xc0;
    default:
      lj_assertA(0, "bad type for src1 (%d)", type);
      return 0;
    }
  }
}

static uint32_t emit_src2(ASMState *as, E2kOp type, intptr_t src2)
{
  if (type == E2K_REG) {
    switch (get_reg_type(src2)) {
    case E2K_REG_B:
      return src2 - RID_B0;
    case E2K_REG_R:
      return (src2 - RID_R0) | 0x80;
    case E2K_REG_G:
      return (src2 - RID_G16 + 16) | 0xe0;
    default:
      lj_assertA(0, "bad reg for src2 (%d)", src2);
      return 0;
    }
  } else {
    switch (get_const_type(src2)) {
    case E2K_CONST4:
      return src2 | 0xc0;
    case E2K_CONST5: case E2K_CONST16:
      return (emit_lts(as, E2K_CONST16, src2) | 0xd0);
    case E2K_CONST32:
      return (emit_lts(as, E2K_CONST32, src2) | 0xd8);
    case E2K_CONST64:
      return (emit_lts(as, E2K_CONST64, src2) | 0xdc);
    default:
      lj_assertA(0, "bad type for src2 (%d)", type);
      return 0;
    }
  }
}

static uint32_t emit_src3(ASMState *as, E2kOp type, intptr_t src3)
{
  UNUSED(as);
  if (type == E2K_REG) {
    switch (get_reg_type(src3)) {
    case E2K_REG_B:
      return src3 - RID_B0;
    case E2K_REG_R:
      return (src3  - RID_R0) | 0x80;
    case E2K_REG_G:
      return (src3 - RID_G16 + 16) | 0xe0;
    default:
      lj_assertA(0, "bad reg for src3 (%d)", dst);
    }
  } else {
    lj_assertA(0, "bad type for src3 (%d)", type);
  }
}

static uint32_t emit_dst(ASMState *as, E2kOp type, intptr_t dst)
{
  UNUSED(as);
  if (type == E2K_REG) {
    switch (get_reg_type(dst)) {
    case E2K_REG_B:
      return dst - RID_B0;
    case E2K_REG_R:
      return (dst - RID_R0) | 0x80;
    case E2K_REG_CTPR:
      return (dst - RID_CTPR1 + 1) | 0xd0;
    case E2K_REG_G:
      return (dst - RID_G16 + 16) | 0xe0;
    default:
      lj_assertA(0, "bad reg for dst (%d)", dst);
    }
  } else {
    lj_assertA(0, "bad type for dst (%d)", type);
  }
}

static uint32_t emit_pdst(ASMState *as, E2kOp type, intptr_t pred)
{
  UNUSED(as);
  if (type == E2K_REG_PRED) {
    return pred - RID_PRED1 + 1;
  } else {
    lj_assertA(0, "bad reg for pdst (%d)", pred);
    return 0;
  }
}

static void emit_alopf7(ASMState *as, uint32_t spec, uint32_t cop, uint32_t opce,
                        uint32_t mask, uint32_t src1, uint32_t src2, uint32_t pred)
{
  int als_idx = emit_als(as, mask);
  E2kAlopf7 syl;
  syl.i = 0;
  syl.fields.pdst = pred;
  syl.fields.cmpopce = opce;
  syl.fields.src2 = src2;
  syl.fields.src1 = src1;
  syl.fields.cop = cop;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
}

static void emit_alopf3(ASMState *as, uint32_t spec, uint32_t cop, uint32_t mask,
                        uint32_t src1, uint32_t src2, uint32_t src3)
{
  int als_idx = emit_als(as, mask);
  E2kAlopf3 syl;
  syl.i = 0;
  syl.fields.src3  = src3;
  syl.fields.src2 = src2;
  syl.fields.src1 = src1;
  syl.fields.cop = cop;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
}

static void emit_alopf2(ASMState *as, uint32_t spec, uint32_t cop, uint32_t opce,
                        uint32_t mask, uint32_t src2, uint32_t dst)
{
  int als_idx = emit_als(as, mask);
  E2kAlopf2 syl;
  syl.i = 0;
  syl.fields.dst  = dst;
  syl.fields.src2 = src2;
  syl.fields.opce = opce;
  syl.fields.cop = cop;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
}

static void emit_alopf1(ASMState *as, uint32_t spec, uint32_t cop,
                        uint32_t mask, uint32_t src1, uint32_t src2, uint32_t dst)
{
  int als_idx = emit_als(as, mask);
  E2kAlopf1 syl;
  syl.i = 0;
  syl.fields.dst  = dst;
  syl.fields.src2 = src2;
  syl.fields.src1 = src1;
  syl.fields.cop = cop;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
}

static void emit_ct(ASMState *as, Reg ctpr, Reg pred, int inverted)
{
  // TODO it takes not a full syl
  check_resource(as, RES_SS);
  E2kSS syl;
  syl.i = 0;
  if (pred) { /* RID_PREDX is nonnull  */
    // do not check loop_end and so on right now
    if (inverted) {
      syl.fields.ctcond = 0x60 + (pred - RID_PRED0);
    } else {
      syl.fields.ctcond = 0x40 + (pred - RID_PRED0);
    }
  } else {
    syl.fields.ctcond = 0x20; // unconditional
  }
  syl.fields.ctop = ctpr - RID_CTPR1 + 1;
  syl.fields.ipd = 3;

  as->bundle.ss = syl.i;
  as->bundle.f1++;
}

static void emit_copf2(ASMState *as, uint32_t opc, Reg ctpr, uintptr_t disp)
{
  check_resource(as, RES_CS0);
  E2kCopf2 syl;
  syl.i = 0;
  syl.fields.disp = disp >> 3;
  syl.fields.opc = opc;
  syl.fields.ctpr = ctpr - RID_CTPR1 + 1;

  as->bundle.cs[0] = syl.i;
  as->bundle.f1++;
}

#define emit_nop(as, nops) \
  as->bundle.nop = nops

/* -- Emit loads/stores --------------------------------------------------- */

#define emit_canremat(ref)  ((ref) <= REF_BASE)

static void emit_loadu64(ASMState *as, Reg r, uint64_t u64)
{
  NIY
}

static void emit_loadk64(ASMState *as, Reg r, IRIns *ir)
{
  NIY
}

static void emit_opgl(ASMState *as, Reg r, void *p)
{
  NIY
}

#define emit_getgl(as, r, field) emit_opgl(as, r, (void *)&J2G(as->J)->field)
#define emit_setgl(as, r, field) emit_opgl(as, r, (void *)&J2G(as->J)->field)
#define emit_setvmstate(as, i) UNUSED(i)

static void emit_loadi(ASMState *as, Reg r, uint64_t u64)
{
  NIY
}

static void emit_loadofs(ASMState *as, IRIns *ir, Reg r, Reg base, int32_t ofs)
{
  NIY
}

static void emit_storeofs(ASMState *as, IRIns *ir, Reg r, Reg base, int32_t ofs)
{
  NIY
}

static void emit_jmp(ASMState *as,  MCode *target)
{
  NIY
}

/* -- Emit generic operations --------------------------------------------- */

/* Generic move between two regs. */
static void emit_movrr(ASMState *as, IRIns *ir, Reg dst, Reg src)
{
  UNUSED(ir);
  emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
              emit_src1(as, E2K_REG, src),
              emit_src2(as, E2K_CONST, 0),
              emit_dst(as, E2K_REG, dst));
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

/* Add offset to pointer. */
static void emit_addptr(ASMState *as, Reg r, int32_t ofs)
{
  if (ofs) {
    NIY
  }
}

#define emit_spsub(as, ofs) emit_addptr(as, 0, -(ofs))
