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
  [0x10] = { "adds",     "ALOPF1" },
  [0x11] = { "addd",     "ALOPF1" },
  [0x1d] = { "sard",     "ALOPF1" },
  [0x20] = { "cmpsb",    "ALOPF7" },
  [0x21] = { "cmpdb",    "ALOPF7" },
  [0x22] = { "cmpandsb", "ALOPF7" },
  [0x23] = { "cmpanddb", "ALOPF7" },
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
  [0x67] = { "ldd",      "ALOPF1" },
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

local function get_word(ctx, pos)
  local b0, b1, b2, b3 = byte(ctx.code, pos+1, pos+4)
  return bor(lshift(b3, 24), lshift(b2, 16), lshift(b1, 8), b0) 
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

local function print_src2(ctx, src2, lts_pos)
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
    local code = ctx:get(lts_pos - lshift(lts_n + 1, 2))
    if band(src2, 0x4) == 0 then
      return format("lts%d_lo 0x%x", lts_n, band(code, 0xffff))
    else
      return format("lts%d_hi 0x%x", lts_n, rshift(band(code, 0xffff0000), 16))
    end
  elseif band(src2, 0xfc) == 0xd8 then
    local lts_n = band(src2, 0x3)
    local code = ctx:get(lts_pos - lshift(lts_n + 1, 2))
    return format("lts%d 0x%x", lts_n, code)
  elseif band(src2, 0xfc) == 0xdc then
    local lts_n = band(src2, 0x3)
    local code_lo = ctx:get(lts_pos - lshift(lts_n + 1, 2))
    local code_hi = ctg:get(lts_pos - lshift(lts_n + 2, 2))
    return format("lts%d-%d 0x%x%x", lts_n, lts_n+1, code_hi, code_lo)
  else
    error("unrecognized src2")
  end
end

local function print_src3(ctx, src1)
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

-- Output ALU operations.
local function print_als(ctx)
  local pos, als, lts_pos = ctx.als_pos, ctx.als, ctx.lts_pos
  local op, als_n = "", 0
  while als ~= 0 do
    if band(als, 1) then
      local code = ctx:get(pos)
      local spec = band(rshift(code, 31), 0x1)
      local cop = band(rshift(code, 24), 0x7f)
      if map_op[cop] then
        local fmt = map_op[cop][2]
        if fmt == "ALOPF1" then
          local src1 = print_src1(ctx, band(rshift(code, 16), 0xff))
          local src2 = print_src2(ctx, band(rshift(code, 8), 0xff), lts_pos)
          local dst  = print_dst(ctx, band(code, 0xff))
          op = map_op[cop][1]
          if spec == 1 then op = op..",sm" end
          op = format("%s %s, %s, %s", op, src1, src2, dst)
        elseif fmt == "ALOPF2" then
          local opce = band(rshift(code, 16), 0xff)
          local src2 = print_src2(ctx, band(rshift(code, 8), 0xff), lts_pos)
          local dst  = print_dst(ctx, band(code, 0xff))
          op = map_op[cop][1]
          if     op == "fstos" then op = map_fsd[opce][1]
          elseif op == "fstod" then op = map_fsd[opce][2]
          elseif op == "fdtos" then op = map_fsd[opce][3]
          elseif op == "fdtod" then op = map_fsd[opce][4]
          end
          if spec == 1 then op = op..",sm" end
          op = format("%s %s, %s", op, src2, dst)
        elseif fmt == "ALOPF3" then
          local src1 = print_src1(ctx, band(rshift(code, 16), 0xff))
          local src2 = print_src2(ctx, band(rshift(code, 8), 0xff), lts_pos)
          local src3 = print_src3(ctx, band(code, 0xff))
          op = map_op[cop][1]
          if spec == 1 then op = op..",sm" end
          op = format("%s %s, %s, %s", op, src1, src2, src3)
        elseif fmt == "ALOPF7" then
          local src1 = print_src1(ctx, band(rshift(code, 16), 0xff))
          local src2 = print_src2(ctx, band(rshift(code, 8), 0xff), lts_pos)
          local opce = band(rshift(code, 5), 0x7)
          local pdst = print_pdst(ctx, band(code, 0x1f))
          op = map_op[cop][1]
          if     op == "cmpsb" then op = map_cmp[opce][1]
          elseif op == "cmpdb" then op = map_cmp[opce][2]
          elseif op == "cmpandsb" then op = map_cmp[opce][3]
          elseif op == "cmpanddb" then op = map_cmp[opce][4]
          elseif op == "fcmpsb" then op = map_cmp[opce][5]
          elseif op == "fcmpdb" then op = map_cmp[opce][6]
          end
          if spec == 1 then op = op..",sm" end
          op = format("%s %s, %s, %s", op, src1, src2, pdst)
        end
      else
        op = "unrecognized"
      end
      ctx.out(format("alc%d:   %s\n", als_n, op))
    end
    als_n = als_n + 1
    pos = pos + 4
    als = rshift(als, 1)
  end
  return pos
end

-- Output control operations.
local function print_cs(ctx)
  local ct, ss_ctpr, pred, inv = false, nil, nil, ""
  if ctx.ss ~= 0 then
    -- ignore most format of ss, we need here only control transfer
    local code = ctx:get(ctx.ss_pos)
    local ctop = band(rshift(code, 5), 0x3) -- only always, pred, ipred
    local psrc = band(code, 0x1f)
    if ctop ~= 0 then
      ct, ss_ctpr = true, band(rshift(code, 10), 0x3)
      if ctop == 2 then pred = psrc
      elseif ctop == 3 then pred, inv  = psrc, "~"
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
      local p = ""
      local sym = ctx.symtab[ctx.addr + ctx.pos + disp]
      if op == "ibranch" then ct = false end
      if pred then p = format(", %s%%pred%d", inv, pred) end
      ctx.out(format("cs0+ss: %s ->%s%s\n", op, sym, p))
    else
      if op == "sdisp" then
        ctx.out(format("cs0:    %s %%ctpr%d, %s\n", op, ctpr, band(code, 0x1f)))
      elseif op == "return" then
        ctx.out(format("cs0:    %s %%ctpr%d\n", op, ctpr))
      else
        local sym = ctx.symtab[ctx.addr + ctx.pos + disp]
        ctx.out(format("cs0:    %s %%ctpr%d, %s\n", op, ctpr, sym))
      end
    end
    pos = pos + 4
  end
  if band(ctx.cs, 0x2) == 0x2 then
    -- ignore most of cases, jit uses only call here
    local code = ctx:get(pos)
    local opc = band(rshift(code, 28), 0xf)
    local wbs = band(code, 0x7f)
    -- ctpr is in SS
    -- TODO predicates from SS ctpr from SS
    -- TODO case for SS ct only
    error("NIY")
  end
end

-- Disassemble  a single wide instruction.
local function disass_ins(ctx)
  local hex, ofs, pos = "", 0, ctx.pos
  local hs = ctx:get(pos)
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
    hex = hex.." "..tohex(ctx:get(pos + ofs))
    ofs = ofs + 4
  end

  ctx.epos = ctx.pos + ofs
  if ctx.hexdump == 0 then hex = "" end
  ctx.out(format("%08x: %s\n", ctx.addr + pos, hex))
  -- its v3 style so ignoring ALES2/5 and cs1 right after cs0
  ctx.ss_pos  = pos + 4
  ctx.als_pos = ctx.ss_pos + lshift(ctx.ss, 2)
  ctx.cs_pos = ctx.als_pos
  ctx.lts_pos = ctx.epos - lshift(ctx.cds + ctx.pl , 2)
  if ctx.als ~= 0 then
    ctx.cs_pos = print_als(ctx)
  end
  if ctx.cs ~= 0 then print_cs(ctx) end
  ctx.pos = ctx.epos 
end

------------------------------------------------------------------------------

-- Disassemble a block of code.
local function disass_block(ctx, ofs, len)
  if not ofs then ofs = 0 end
  local stop = len and ofs+len or #ctx.code
  ctx.pos = ofs
  while ctx.pos < stop do
    ctx.epos = nil
    ctx.als, ctx.ales, ctx.pl, ctx.cds = nil, nil, nil, nil
    ctx.ss, ctx.nop, ctx.lng, ctx.mdl = nil, nil, nil, nil
    ctx.cs_pos = nil
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
  return ctx
end

-- Simple API: disassemble code (a string) at address and output via out.
local function disass(code, addr, out)
  create(code, addr, out):disass()
end

-- Public module functions.
return {
  create = create,
  disass = disass,
}
