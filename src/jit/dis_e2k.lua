----------------------------------------------------------------------------
-- LuaJIT E2K disassembler module.
--
-- Copyright (C) 2005-2025 Mike Pall. All rights reserved.
-- Released under the MIT/X license. See Copyright Notice in luajit.h
----------------------------------------------------------------------------
-- This is a helper module used by the LuaJIT machine code dumper module.
--
-- It disassebles only common instructions used in JIT itself
------------------------------------------------------------------------------

local byte, format = string.byte, string.format
local bit = require("bit")
local band, bor, tohex = bit.band, bit.bor, bit.tohex
local lshift, rshift = bit.lshift, bit.rshift

------------------------------------------------------------------------------
-- Opcode maps
------------------------------------------------------------------------------

-- Some of operations use the same opcode but for different channels, ignore
-- those, coas all of them are not used in jit

local map_op = {
-- opc        name        format
  [0x00] = { "ands",     "ALOPF1" },
  [0x01] = { "andd",     "ALOPF1" },
  [0x02] = { "andns",    "ALOPF1" },
  [0x03] = { "andnd",    "ALOPF1" },
  [0x04] = { "ors",      "ALOPF1" },
  [0x05] = { "ord",      "ALOPF1" },
  [0x06] = { "orns",     "ALOPF1" },
  [0x07] = { "ornd",     "ALOPF1" },
  ----------------------------------
  [0x08] = { "xors",     "ALOPF1" },
  [0x09] = { "xord",     "ALOPF1" },
  [0x0a] = { "xorns",    "ALOPF1" },
  [0x0b] = { "xornd",    "ALOPF1" },
  [0x0c] = { "sxt",      "ALOPF1" },
  [0x0e] = { "merges",   "ALOPF1" },
  [0x0f] = { "merged",   "ALOPF1" },
  ----------------------------------
  [0x10] = { "adds",     "ALOPF1" },
  [0x11] = { "addd",     "ALOPF1" },
  [0x12] = { "subs",     "ALOPF1" },
  [0x13] = { "subd",     "ALOPF1" },
  [0x14] = { "scls",     "ALOPF1" },
  [0x15] = { "scld",     "ALOPF1" },
  [0x16] = { "scrs",     "ALOPF1" },
  [0x17] = { "scrd",     "ALOPF1" },
  ----------------------------------
  [0x18] = { "shls",     "ALOPF1" },
  [0x19] = { "shld",     "ALOPF1" },
  [0x1a] = { "shrs",     "ALOPF1" },
  [0x1b] = { "shrd",     "ALOPF1" },
  [0x1c] = { "sars",     "ALOPF1" },
  [0x1d] = { "sard",     "ALOPF1" },
  [0x1e] = { "getfs",    "ALOPF1" },
  [0x1f] = { "getfd",    "ALOPF1" },
  ----------------------------------
  [0x20] = { "cmpsb",    "ALOPF7" },
  [0x21] = { "cmpdb",    "ALOPF7" },
  [0x22] = { "cmpandsb", "ALOPF7" },
  [0x23] = { "cmpanddb", "ALOPF7" },
  [0x24] = { "stb",      "ALOPF3" },
  [0x25] = { "sth",      "ALOPF3" },
  [0x26] = { "stw",      "ALOPF3" },
  [0x27] = { "std",      "ALOPF3" },
  ----------------------------------
  [0x2e] = { "fcmpsb",   "ALOPF7" },
  [0x2f] = { "fcmpdb",   "ALOPF7" },
  ----------------------------------
  [0x30] = { "fadds",    "ALOPF1" },
  [0x31] = { "faddd",    "ALOPF1" },
  [0x32] = { "fsubs",    "ALOPF1" },
  [0x33] = { "fsubd",    "ALOPF1" },
  [0x34] = { "fmins",    "ALOPF1" },
  [0x35] = { "fmind",    "ALOPF1" },
  [0x36] = { "fmaxs",    "ALOPF1" },
  [0x37] = { "fmaxd",    "ALOPF1" },
  ----------------------------------
  [0x38] = { "fmuls",    "ALOPF1" },
  [0x39] = { "fmuld",    "ALOPF1" },
  [0x3c] = { "fstos",    "ALOPF2" },
  [0x3d] = { "fdtod",    "ALOPF2" },
  [0x3e] = { "fstod",    "ALOPF2" },
  [0x3f] = { "fdtos",    "ALOPF2" },
  ----------------------------------
  [0x61] = { "movtd",    "ALOPF2" },
  [0x64] = { "ldb",      "ALOPF1" },
  [0x65] = { "ldh",      "ALOPF1" },
  [0x66] = { "ldw",      "ALOPF1" },
  [0x67] = { "ldd",      "ALOPF1" },
}

local map_opext = {
-- opc2       opc        name      format    opce2
  [0x01] = {
             [0x20] = { "muls",    "ALOPF11", 0xc0 },
             [0x21] = { "muld",    "ALOPF11", 0xc0 },
             [0x22] = { "umulx",   "ALOPF11", 0xc0 },
             [0x23] = { "smulx",   "ALOPF11", 0xc0 },
-----------------------------------------------------
             [0x49] = { "fdivd",   "ALOPF11", 0xc0 },
             [0x4d] = { "fsqrtid", "ALOPF12", 0xc0 }, -- ignore opce
             [0x51] = { "fsqrttd", "ALOPF11", 0xc0 }, -- ignore opce
             [0x58] = { "getsp",   "ALOPF12", 0xc0 }, -- ignore opce
             [0x6d] = { "fdtoifd", "ALOPF11", 0xc0 }, -- ignore opce
  },
-- PFCMB1
  [0x0f] = {
             [0x4d] = { "pshufb",  "ALOPF21", 0x00 },

  },
}

local map_fsd = {
-- opce      "fstos"       "fstod"     "fdtos"      "fdtod"
  [0xc0] = { "fstois",     "fstoid",   "fdtois",    "fdtoid"     },
  [0xc1] = { nil,          nil,        "fxtois",    "fxtoid"     },
  [0xc2] = { "fstoistr",   "fstoidtr", "fdtoistr",  "fdtoidtr"   },
  [0xc3] = { nil,          nil,        "fxtoistr",  "fxtoidtr"   },
  [0xc4] = { "istofs",     "istofd",   "idtofs",    "idtofd"     },
  [0xc5] = { nil,          "istofx",   nil,         "idtofx"     },
  [0xc6] = { nil,          "fstofd",   "fdtofs",    "fxtofd"     },
  [0xc7] = { nil,          "fstofx",   "fxtofs",    "fdtofx"     },
  [0xc8] = { nil,          nil,        "pfdtois",   "pfstois"    },
  [0xc9] = { nil,          nil,        nil,         nil          },
  [0xca] = { nil,          nil,        "pfdtoistr", "pfstoistr"  },
  [0xcb] = { nil,          nil,        nil,         nil          },
  [0xcc] = { nil,          nil,        nil,         "pistofs"    },
  [0xcd] = { nil,          nil,        nil,         nil          },
  [0xce] = { nil,          "pfstofd",  "pfdtofs",   nil          },
  [0xcf] = { "fstofxtofs", nil,        nil,         "fdtofxtofd" },
}

local map_cmp = {
-- ignored cctob and fxcmp(s/d/x)b
-- opce     "cmpsb"    "cmpdb"    "cmpandsb"    "cmpanddb"    "fcmpsb"     "fcmpdb"
  [0x0] = { "cmposb",  "cmpodb",  nil,          nil,          "fcmpeqsb",  "fcmeqdb"   },
  [0x1] = { "cmpbsb",  "cmpbdb",  nil,          nil,          "fcmpltsb",  "fcmpltdb"  },
  [0x2] = { "cmpesb",  "cmpedb",  "cmpandesb",  "cmpandedb",  "fcmplesb",  "fcmpledb"  },
  [0x3] = { "cmpbesb", "cmpbedb", nil,          nil,          "fcmpuodsb", "fcmpuoddb" },
  [0x4] = { "cmpssb",  "cmpsdb",  "cmpandssb",  "cmpandsdb",  "fcmpneqsb", "fcmpneqdb" },
  [0x5] = { "cmppsb",  "cmppdb",  "cmpandpsb",  "cmpandpdb",  "fcmpnltsb", "fcmpnltdb" },
  [0x6] = { "cmplsb",  "cmpldb",  nil,          nil,          "fcmpnlesb", "fcmpnledb" },
  [0x7] = { "cmplesb", "cmpledb", "cmpandlesb", "cmpandledb", "fcmpodsb",  "fcmpoddb"  },
}

local map_cs0 = {
  [0] = { "ibranch", "pref",  "puttsd", "done"   },
  [1] = { "disp",    nil,     "sdisp",  "gettsd" },
  [2] = { "disp",    "ldisp", "sdisp",  "gettsd" },
  [3] = { "disp",    nil,     "sdisp",  "return" },
}

local map_cs1 = {
  [0] = "setr0", [1] = "setr1", [2] = "setei", [3] = "wait", [4] = "setbr",
  [5] = "call",  [6] = "mas",   [7] = "flushr", [8] = "bg",
}

local map_ridregname = {
  [0] = "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7",
  "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
  "r52", "r53", "r54", "r55", "r56", "r57", "r58", "r59",
  "b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7",
  "b8", "b9", "b10", "b11", "b12", "b13", "b14", "b15",
  "g16", "g17", "g18", "g19",
  "pred0", "pred1", "pred2", "pred3",
  "ctpr1", "ctpr2", "ctpr3",
}

------------------------------------------------------------------------------

local function get_halfword(ctx, pos)
  if ctx.half_hi then
    local b3, b4 = byte(ctx.code, pos+3, pos+4)
    ctx.half_hi = false
    return bor(lshift(b4, 8), b3)
  else
    local b0, b1 = byte(ctx.code, pos+1, pos+2)
    ctx.half_hi = true
    return bor(lshift(b1, 8), b0)
  end
end

local function get_word(ctx, pos)
  local b0, b1, b2, b3 = byte(ctx.code, pos+1, pos+4)
  return bor(lshift(b3, 24), lshift(b2, 16), lshift(b1, 8), b0) 
end

local function shex(val)
  local res = tohex(val):gsub("^0+", "")
  if res == "" then return "0" else return res end
end

-- Output operands.
local function print_src1(ctx, src1)
  if band(src1, 0x80) == 0 then
    return format("%%b%d", band(src1, 0x7f))
  elseif band(src1, 0xc0) == 0x80 then
    return format("%%r%d", band(src1, 0x3f))
  elseif band(src1, 0xe0) == 0xe0 then
    return format("%%g%d", band(src1, 0x1f))
  elseif band(src1, 0xe0) == 0xc0 then
    return format("0x%x", band(src1, 0x1f))
  else
    error("unrecognized src1")
  end
end

local function print_src2(ctx, src2)
  if band(src2, 0x80) == 0 then
    return format("%%b%d", band(src2, 0x7f))
  elseif band(src2, 0xc0) == 0x80 then
    return format("%%r%d", band(src2, 0x3f))
  elseif band(src2, 0xe0) == 0xe0 then
    return format("%%g%d", band(src2, 0x1f))
  elseif band(src2, 0xf0) == 0xc0 then
    return format("0x%x", band(src2, 0x0f))
  elseif band(src2, 0xf8) == 0xd0 then
    local lts_n = band(src2, 0x3)
    local code = ctx:get(ctx.lts_pos - lshift(lts_n, 2))
    if band(src2, 0x4) == 0 then
      return format("lts%d_lo 0x%x", lts_n, band(code, 0xffff))
    else
      return format("lts%d_hi 0x%x", lts_n, rshift(band(code, 0xffff0000), 16))
    end
  elseif band(src2, 0xfc) == 0xd8 then
    local lts_n = band(src2, 0x3)
    local code = ctx:get(ctx.lts_pos - lshift(lts_n, 2))
    return format("lts%d 0x%s", lts_n, shex(code))
  elseif band(src2, 0xfc) == 0xdc then
    local lts_n = band(src2, 0x3)
    local code_lo = ctx:get(ctx.lts_pos - lshift(lts_n, 2))
    local code_hi = ctx:get(ctx.lts_pos - lshift(lts_n + 1, 2))
    return format("lts%d-%d 0x%s%s", lts_n, lts_n+1, shex(code_hi), tohex(code_lo))
  else
    error("unrecognized src2")
  end
end

local function print_src3(ctx, src3)
  if band(src3, 0x80) == 0 then
    return format("%%b%d", band(src3, 0x7f))
  elseif band(src3, 0xc0) == 0x80 then
    return format("%%r%d", band(src3, 0x3f))
  elseif band(src3, 0xe0) == 0xe0 then
    return format("%%g%d", band(src3, 0x1f))
  else
    error("unrecognized src3")
  end
end

local function print_dst(ctx, dst)
  if band(dst, 0x80) == 0 then
    return format("%%b%d", band(dst, 0x7f))
  elseif band(dst, 0xc0) == 0x80 then
    return format("%%r%d", band(dst, 0x3f))
  elseif band(dst, 0xe0) == 0xe0 then
    return format("%%g%d", band(dst, 0x1f))
  elseif band(dst, 0xf0) == 0xd0 then
    return format("%%ctpr%d", band(dst, 0x0f))
  elseif dst == 0xdf then
    return format("%%empty")
  else
    error("unrecognized dst")
  end
end

local function print_pdst(ctx, pdst)
  return format("%%pred%d", pdst)
end

local function print_alf1(ctx, code)
  local src1 = print_src1(ctx, band(rshift(code, 16), 0xff))
  local src2 = print_src2(ctx, band(rshift(code, 8), 0xff))
  local dst  = print_dst(ctx, band(code, 0xff))
  return src1, src2, dst
end

local function print_alf2(ctx, code)
  local opce = band(rshift(code, 16), 0xff)
  local src2 = print_src2(ctx, band(rshift(code, 8), 0xff))
  local dst  = print_dst(ctx, band(code, 0xff))
  return opce, src2, dst
end

local function print_alf3(ctx, code)
  local src1 = print_src1(ctx, band(rshift(code, 16), 0xff))
  local src2 = print_src2(ctx, band(rshift(code, 8), 0xff))
  local src3 = print_src3(ctx, band(code, 0xff))
  return src1, src2, src3
end

local function print_alf7(ctx, code)
  local src1 = print_src1(ctx, band(rshift(code, 16), 0xff))
  local src2 = print_src2(ctx, band(rshift(code, 8), 0xff))
  local opce = band(rshift(code, 5), 0x7)
  local pdst = print_pdst(ctx, band(code, 0x1f))
  return src1, src2, opce, pdst
end

local function print_alef1(ctx, code)
  return print_src3(ctx, band(code, 0xff))
end

local function print_alef2(ctx, code)
  return band(code, 0xff)
end

-- Output ALU operations.
local function print_als(ctx)
  local als, als_pos = ctx.als, ctx.als_pos
  local ales, ales_pos = ctx.ales, ctx.ales_pos
  local als_n, cds, cds_pos = 0, ctx.cds, ctx.cds_pos
  -- get pridicates
  local pred = { nil, nil, nil, nil, nil, nil }
  ctx.half_hi = true
  while cds ~= 0 do
    local code = ctx:geth(cds_pos)
    if code ~= 0 then
      local opc = band(rshift(code, 14), 0x3)
      local mask = band(rshift(code, 10), 0xf)
      local neg = band(rshift(code, 7), 0x7)
      local pr = band(code, 0x1f) -- only psrc
      local n, c = 0, 0
      if opc == 1 or opc == 3 then c = 3 end
      while mask ~= 0 do
        if band(mask, 0x1) ~= 0 then
          pred[n + 1 + c] = format("%%pred%d", pr)
        end
        mask = rshift(mask, 1)
        n = n + 1
      end
      n = 0
      -- yee it can use the same pred with alternative
      while neg ~= 0 do
        if band(neg, 0x1) ~= 0 then
          pred[n + 1 + c] = format("~%%pred%d", pr)
        end
        neg = rshift(neg, 1)
        n = n + 1
      end
    end
    if ctx.half_hi == true then
      cds_pos = cds_pos - 4
      cds = cds - 1
    end
  end
  ctx.half_hi = true
  while als ~= 0 do
    local name, ops = nil, nil
    if band(als, 1) ~= 0 then
      local code = ctx:get(als_pos)
      local spec = band(rshift(code, 31), 0x1)
      local cop = band(rshift(code, 24), 0x7f)
      if band(ales, 1) ~= 0 then
        local ales_code = ctx:geth(ales_pos)
        local opc2 = 0x01 -- default opc2 for ALES2/ALES5
        if als_n ~= 2 and als_n ~= 5 then
          opc2 = band(rshift(ales_code, 8), 0xff)
        end
        if map_opext[opc2] and map_opext[opc2][cop] then
          local fmt = map_opext[opc2][cop][2]
          if fmt == "ALOPF11" then
            local src1, src2, dst = print_alf1(ctx, code)
            local opce2 = print_alef2(ctx, ales_code)
            name = map_opext[opc2][cop][1]
            ops = format("%s, %s, %s", src1, src2, dst)
          elseif fmt == "ALOPF12" then
            local opce, src2, dst = print_alf2(ctx, code)
            local opce2 = print_alef2(ctx, ales_code)
            name = map_opext[opc2][cop][1]
            ops = format("%s, %s", src2, dst)
          elseif fmt == "ALOPF21" then
            local src1, src2, dst = print_alf1(ctx, code)
            local src3 = print_alef1(ctx, ales_code)
            name = map_opext[opc2][cop][1]
            ops = format("%s, %s, %s, %s", src1, src2, src3, dst)
          end
        end
        if ctx.half_hi then ales_pos = ales_pos + 4 end
      else
        if map_op[cop] then
          local fmt = map_op[cop][2]
          if fmt == "ALOPF1" then
            name = map_op[cop][1]
            ops = format("%s, %s, %s", print_alf1(ctx, code))
          elseif fmt == "ALOPF2" then
            local opce, src2, dst = print_alf2(ctx, code)
            if cop >= 0x3c and cop <= 0x3f then
              name = map_fsd[opce][cop - 0x3c + 1]
            else
              name = map_op[cop][1]
            end
            ops = format("%s, %s", src2, dst)
          elseif fmt == "ALOPF3" then
            name = map_op[cop][1]
            ops = format("%s, %s, %s", print_alf3(ctx, code))
          elseif fmt == "ALOPF7" then
            local src1, src2, opce, pdst = print_alf7(ctx, code)
            if cop >= 0x20 and cop <= 0x23 then
              name = map_cmp[opce][cop - 0x20 + 1]
            elseif cop >= 0x2e and cop <= 0x2f then
              name = map_cmp[opce][cop - 0x2e + 5]
            else
              name = map_op[cop][1]
            end
            ops = format("%s, %s, %s", src1, src2, pdst)
          end
        end
      end
      if not name then name = "unrecognized" end
      name = name..","..als_n
      if spec == 1 then name = name..",sm" end
      als_pos = als_pos + 4
      if pred[als_n + 1] then ops = ops.." ? "..pred[als_n + 1] end
      ctx.out(format("        %s %s\n", name, ops))
    end
    als_n = als_n + 1
    als = rshift(als, 1)
    ales = rshift(ales, 1)
  end
  return als_pos
end

-- Output control operations.
local function print_cs(ctx)
  local ct, ss_ctpr, pred  = false, nil, ""
  if ctx.ss ~= 0 then
    -- ignore most format of ss, we need here only control transfer
    local code = ctx:get(ctx.ss_pos)
    local ctop = band(rshift(code, 5), 0x3) -- only always, pred, ipred
    local psrc = band(code, 0x1f)
    if ctop ~= 0 then
      ct, ss_ctpr = true, band(rshift(code, 10), 0x3)
      if ctop == 2 then pred = format(" ? %%pred%d", psrc)
      elseif ctop == 3 then pred = format(" ? ~%%pred%d", psrc)
      end
    end
  end

  local pos = ctx.cs_pos
  if band(ctx.cs, 0x1) == 0x1 then
    local code = ctx:get(pos)
    local ctpr = band(rshift(code, 30), 0x3)
    local opc  = band(rshift(code, 28), 0x3)
    local disp = lshift(band(code, 0xfffffff), 3)
    if band(disp, 0x8000000) ~= 0 then
      disp = bor(disp, 0xf0000000)
    end
    local op = map_cs0[ctpr][opc + 1]
    if ctpr == 0 then
      local addr = ctx.addr + ctx.pos + disp
      local sym = ctx.symtab[addr]
      if not sym then sym = format("0x%x", addr) end
      if op == "ibranch" then ct = false end
      ctx.out(format("        %s ->%s%s\n", op, sym, pred))
    else
      if op == "sdisp" then
        ctx.out(format("        %s %%ctpr%d, %s\n", op, ctpr, band(code, 0x1f)))
      elseif op == "return" then
        ctx.out(format("        %s %%ctpr%d\n", op, ctpr))
      else
        local sym = ctx.symtab[ctx.addr + ctx.pos + disp]
        ctx.out(format("        %s %%ctpr%d, %s\n", op, ctpr, sym))
      end
    end
    pos = pos + 4
  end
  if band(ctx.cs, 0x2) == 0x2 then
    -- ignore most of cases, jit uses only call here
    local code = ctx:get(pos)
    local opc = band(rshift(code, 28), 0xf)
    local wbs = band(code, 0x7f)
    local name = map_cs1[opc]
    if name == "call" then
      ct = false
      ctx.out(format("        %s %%ctpr%d, wbs = %d%s\n", name, ss_ctpr, wbs, pred))
    else
      ctx.out("        unrecognized\n")
    end
  end

  -- if neither ibranch nor call, but ctop than print ct
  if ct == true then ctx.out(format("        ct %%ctpr%d%s\n", ss_ctpr, pred)) end
end

local function print_nop(ctx)
  ctx.out("        nop %d\n", ctx.nop)
end

-- Disassemble  a single wide instruction.
local function disass_ins(ctx)
  local hex, ofs= "", 0
  local hs = ctx:get(ctx.pos)
  -- get hs fields
  ctx.als = band(rshift(hs, 26), 0x3f)
  ctx.ales = band(rshift(hs, 20), 0x3f)
  ctx.pl = band(rshift(hs, 18), 0x3)
  ctx.cds = band(rshift(hs, 16), 0x3)
  ctx.cs = band(rshift(hs, 14), 0x3)
  ctx.ss = band(rshift(hs, 12), 0x1)
  ctx.nop = band(rshift(hs, 7), 0x7)
  ctx.lng = lshift((band(rshift(hs, 4), 0x7) + 1), 1)
  ctx.mdl = band(hs, 0xf) + 1

  for i=0,ctx.lng-1 do
    hex = hex.." "..tohex(ctx:get(ctx.pos + ofs))
    ofs = ofs + 4
  end

  ctx.epos = ctx.pos + ofs
  if ctx.hexdump == 0 then hex = "" end
  ctx.out(format("%08x: %s\n", ctx.addr + ctx.pos, hex))
  -- its v3 style so ignoring ALES2/5 and cs1 right after cs0
  ctx.ss_pos  = ctx.pos + 4
  ctx.als_pos = ctx.ss_pos + lshift(ctx.ss, 2)
  ctx.cs_pos = ctx.als_pos
  ctx.ales_pos = ctx.pos + lshift(ctx.mdl, 2)
  -- pos from the end
  ctx.cds_pos = ctx.epos - 4
  ctx.lts_pos = ctx.epos - 4 - lshift(ctx.cds + ctx.pl, 2)
  if ctx.als ~= 0 then
    ctx.cs_pos = print_als(ctx)
  end
  if ctx.cs ~= 0 then print_cs(ctx) end
  if ctx.nop ~= 0 then print_nop(ctx) end
  -- if instrunction is empty its nop
  if hs == 0x0 then ctx.out("        nop\n") end
  ctx.pos = ctx.epos 
end

------------------------------------------------------------------------------

-- Disassemble a block of code.
local function disass_block(ctx, ofs, len)
  if not ofs then ofs = 0 end
  local stop = len and ofs+len or #ctx.code
  ctx.pos = ofs
  while ctx.pos < stop do
    ctx.als, ctx.ales, ctx.pl, ctx.cds = nil, nil, nil, nil
    ctx.ss, ctx.nop, ctx.lng, ctx.mdl = nil, nil, nil, nil
    ctx.epos, ctx.ss_pos, ctx.als_pos, ctx.cs_pos  = nil, nil, nil, nil
    ctx.ales_pos, ctx.cds_pos, ctx.lts_pos = nil, nil, nil
    disass_ins(ctx)
  end
end

-- Extended API: create a disassembler context. Then call ctx:disass(ofs, len).
local function create(code, addr, out)
  local ctx = {}
  ctx.code = code
  ctx.addr = addr or 0
  ctx.out = out or io.write
  ctx.symtab = {}
  ctx.disass = disass_block
  ctx.hexdump = 16
  ctx.ct = nil
  ctx.get = get_word
  ctx.geth = get_halfword
  ctx.half_hi = true
  return ctx
end

-- Simple API: disassemble code (a string) at address and output via out.
local function disass(code, addr, out)
  create(code, addr, out):disass()
end

-- Return register name for RID.
local function regname(r)
  return map_ridregname[r]
end

-- Public module functions.
return {
  create = create,
  disass = disass,
  regname = regname,
}
