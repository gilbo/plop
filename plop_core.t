--[[
  plop - A Small Langauge for abstracting over byte-by-byte details of
          physical layout
    
    See interface description at the end of this file for more information
    by Gilbert Bernstein
    March 2016
    
  See LICENSE
--]]

import 'adt'

local Exports = {}
package.loaded["plop_core"] = Exports
--local C = terralib.includecstring [[ #include <stdio.h> ]]

local newlist = terralib.newlist

--local function clone_list(xs)
--  return newlist{ unpack(xs) }
--end
--local function clone_tbl(xs)
--  local cp = {}
--  for k,v in pairs(xs) do cp[k] = v end
--  return cp
--end
local function printtbl(xs)
  for k,v in pairs(xs) do print(k,v) end
end
--local function sorted_pairs(xs)
--  local ps = newlist()
--  for k,v in pairs(xs) do ps:insert{k,v} end
--  ps:sort(function(a,b) return a[1]<b[1] end)
--  local i=0
--  return function()
--    i = i+1
--    local p = ps[i]
--    if p then return p[1],p[2]
--         else return nil end
--  end
--end

local niltoken      = {}
local lookuptoken   = {}
local function nilconvert(val) return val==nil and niltoken or val end

-- function must return exactly one value
-- function must take at least idx_arguments
local function memoize_from(idx,f)
  local cache = {}
  local function memoization_wrapper(...)
    local args     = {select(idx,...)}
    local subcache = cache
    for i=1,#args do
      local sub = subcache[nilconvert(args[i])]
      if not sub then
        sub = {}
        subcache[nilconvert(args[i])] = sub
      end
      subcache = sub
    end
    local lookup = subcache[lookuptoken]
    if not lookup then
      lookup = f(...)
      subcache[lookuptoken] = lookup
    end
    return lookup
  end
  return memoization_wrapper
end
local function memoize(f)
  return memoize_from(1,f)
end

local memolist
do
  local memolist_helper = memoize(function(...)
    return newlist{...}
  end)
  memolist = function(xs) return memolist_helper(unpack(xs)) end
end

-------------------------------------------------------------------------------
-- Data Types (ASTs etc.) along with pretty printing
-------------------------------------------------------------------------------

local function is_uint(obj)
  return type(obj) == 'number' and obj%1 == 0 and obj >= 0
end

local function is_id_str(obj)
  return type(obj) == 'string' and string.match(obj,'^[%a_][%w_]*$')
end

local function is_anon_str(obj)
  return type(obj) == 'string' and string.match(obj,'^%d+_%d+$')
end

local function is_var_str(obj) return is_id_str(obj) or is_anon_str(obj) end


---------------------------------------
-- AST-style stuff                   --
---------------------------------------

local ADT A
  Decl  = Array   { sizevar : symbol?, sizetype : Prim?,
                    sizeval : uint?,        typ : Decl }
        | Struct  { entries : Rec* }
        | Ptr     { typ     : Decl }
        | DPrim   { prim    : Prim }
        attributes  { linenumber : uint?,
                      offset     : uint?,
                      filename   : string? }
  Rec   = Def     { name : id_str, typ : Decl }
        | Const   { name : id_str, val : uint  }
        | Chunk   { name : id_str, numerator : id_str, denominator : id_str }
        attributes  { linenumber : uint?,
                      offset     : uint?,
                      filename   : string? }

  Prim  = SIZE
        | UINT
        | INT
        | BOOL
        | FLOAT
        |   SIZE8 |  SIZE16 |  SIZE32 |  SIZE64
        |   UINT8 |  UINT16 |  UINT32 |  UINT64
        |    INT8 |   INT16 |   INT32 |   INT64
        | FLOAT32 | FLOAT64

  extern uint   is_uint
  extern symbol is_var_str
  extern id_str is_id_str
end

local string_to_primitive = {
  [   "size"] =  A.SIZE,
  [   "uint"] =  A.UINT,
  [    "int"] =  A.INT,
  [   "bool"] =  A.BOOL,
  [  "float"] =  A.FLOAT,
  [  "size8"] =  A.SIZE8,
  [ "size16"] =  A.SIZE16,
  [ "size32"] =  A.SIZE32,
  [ "size64"] =  A.SIZE64,
  [  "uint8"] =  A.UINT8,
  [ "uint16"] =  A.UINT16,
  [ "uint32"] =  A.UINT32,
  [ "uint64"] =  A.UINT64,
  [   "int8"] =  A.INT8,
  [  "int16"] =  A.INT16,
  [  "int32"] =  A.INT32,
  [  "int64"] =  A.INT64,
  ["float32"] =  A.FLOAT32,
  ["float64"] =  A.FLOAT64,
  [   "byte"] =  A.UINT8,
}
local all_primitives = newlist()
for n,prim in pairs(string_to_primitive) do
  if n ~= 'byte' then all_primitives:insert(prim) end
end

-- define ugly and pretty strings and set pretty as default
-- ugly may be useful for internal debugging...
for _,T in pairs(A) do T.uglystr = T.__tostring end
for s,p in pairs(string_to_primitive) do
  if s ~= 'byte' then getmetatable(p).__tostring = function() return s end end
end

function A.Array:prettystr(indent)
  local size = self.sizevar and self.sizevar or self.sizeval
  return '['..tostring(size)..']'..self.typ:prettystr(indent)
end
function A.Ptr:prettystr(indent)
  return '*'..self.typ:prettystr(indent)
end
function A.Struct:prettystr(indent)
  indent = (indent or '')
  local substrs = newlist()
  for _,r in ipairs(self.entries) do
    substrs:insert( r:prettystr(indent..'  ') )
  end
  return '{\n'..substrs:concat('\n')..'\n'..indent..'}'
end
function A.Def:prettystr(indent)
  indent = indent or ''
  return indent..tostring(self.name)..' : '..self.typ:prettystr(indent)
end
function A.Const:prettystr(indent)
  indent = indent or ''
  return indent..tostring(self.name)..' = '..tostring(self.val)
end
function A.Chunk:prettystr(indent)
  indent = indent or ''
  return indent..tostring(self.name)..' = '..tostring(self.numerator)..
                                      ' / '..tostring(self.denominator)
end
function A.DPrim:prettystr(indent)
  return tostring(self.prim)
end

A.Array.__tostring  = A.Array.prettystr
A.Struct.__tostring = A.Struct.prettystr
A.Ptr.__tostring    = A.Ptr.prettystr
A.DPrim.__tostring  = A.DPrim.prettystr
A.Def.__tostring    = A.Def.prettystr
A.Const.__tostring  = A.Const.prettystr
A.Chunk.__tostring  = A.Chunk.prettystr

function A.Decl:prettyprint()   print(self:prettystr()) end
function A.Decl:uglyprint()     print(self:uglystr()) end
function A.Rec:prettyprint()    print(self:prettystr()) end
function A.Rec:uglyprint()      print(self:uglystr()) end

local size_prim_table = {
  [ A.SIZE   ] = true,
  [ A.SIZE8  ] = true,
  [ A.SIZE16 ] = true,
  [ A.SIZE32 ] = true,
  [ A.SIZE64 ] = true,
}
local physical_prim_table = {
  [ A.SIZE8   ] = true,
  [ A.SIZE16  ] = true,
  [ A.SIZE32  ] = true,
  [ A.SIZE64  ] = true,
  [ A.UINT8   ] = true,
  [ A.UINT16  ] = true,
  [ A.UINT32  ] = true,
  [ A.UINT64  ] = true,
  [ A.INT8    ] = true,
  [ A.INT16   ] = true,
  [ A.INT32   ] = true,
  [ A.INT64   ] = true,
  [ A.FLOAT32 ] = true,
  [ A.FLOAT64 ] = true,
}
local function is_size_prim(prim) return size_prim_table[prim] ~= nil end
local function is_phys_prim(prim) return physical_prim_table[prim] ~= nil end
local is_prim   = A.Prim.check
local is_dprim  = A.DPrim.check
local is_ptr    = A.Ptr.check
local is_array  = A.Array.check
local is_struct = A.Struct.check
local is_decl   = A.Decl.check
local is_def    = A.Def.check
local is_const  = A.Const.check
local is_chunk  = A.Chunk.check
local is_rec    = A.Rec.check

---------------------------------------
-- Path IR                           --
---------------------------------------

local ADT P
  Token     = DeRef
            | Field { name : symbol }
            | Index { name : symbol }
  Path      = { tokens : Token*, terminal : type_or_const }

  extern symbol         is_var_str
  extern type_or_const  function(obj) return is_prim(obj) or is_uint(obj) end
end

getmetatable(P.DeRef).__tostring = function() return '()' end
function P.Field:__tostring() return '.'..tostring(self.name) end
function P.Index:__tostring() return '['..tostring(self.name)..']' end
function P.Path:__tostring()
  local subs = newlist()
  for _,p in ipairs(self.tokens) do subs:insert(tostring(p)) end
  return subs:concat('')..':'..tostring(self.terminal)
end

local size_num_bound_table = {
  [ A.SIZE   ] = math.huge,
  [ A.SIZE8  ] = math.pow(2,8),
  [ A.SIZE16 ] = math.pow(2,16),
  [ A.SIZE32 ] = math.pow(2,32),
  [ A.SIZE64 ] = math.huge,
}
local function size_bound_of_num(num)
  if      num < math.pow(2,8)   then  return A.SIZE8
  elseif  num < math.pow(2,16)  then  return A.SIZE16
  elseif  num < math.pow(2,32)  then  return A.SIZE32
                                else  return A.SIZE64 end
end

---------------------------------------
-- Expression IR                     --
---------------------------------------

local ADT E
  Expr      = DeRef   { expr  : Expr,   prim  : Prim? }
            | Add     { const : uint,   exprs : Expr* }
            | Mul     { const : uint,   exprs : Expr* }
            | Var     { name  : symbol, type  : SizePrim? }
            | Idx     { name  : symbol, type  : SizePrim? }
            | Const   { val   : uint   }
            | Ptr

  extern uint       is_uint
  extern symbol     is_var_str
  extern Prim       is_prim
  extern SizePrim   is_size_prim
end

-- memoize all expression constructors
local NewE = {}
for _,n in ipairs{'DeRef', 'Add', 'Mul', 'Var', 'Idx', 'Const'} do
  local e = E[n]
  if n=='Add' or n=='Mul' then
    local memed = memoize(e)
    NewE[n] = function(c, xs) return memed(c, memolist(xs)) end
  else
    NewE[n] = memoize(e)
  end
end

local PtrVar = E.Ptr


function E.DeRef:__tostring()
  local typstr = self.prim and '[&'..tostring(self.prim)..']' or ''
  return '@'..typstr..'('..tostring(self.expr)..')'
end
function E.Add:__tostring()
  local estrs = self.exprs:map(tostring):concat('+')
  local conststr = self.const == 0 and "" or tostring(self.const)..'+'
  return conststr..estrs
end
function E.Mul:__tostring()
  local estrs = self.exprs:map(function(e)
    local str = tostring(e)
    if E.Add.check(e) then return '('..str..')' else return str end
  end):concat('*')
  local conststr = self.const == 1 and "" or tostring(self.const)..'*'
  return conststr..estrs
end
function E.Var:__tostring()
  return self.type
          and '('..tostring(self.name).. ':'..tostring(self.type)..')'
          or tostring(self.name)
end
function E.Idx:__tostring()
  return self.type
          and '('..tostring(self.name).. ':'..tostring(self.type)..')'
          or tostring(self.name)
end
function E.Const:__tostring()   return self.val end

local is_econst = E.Const.check
local is_evar   = E.Var.check
local is_eidx   = E.Idx.check
local is_emul   = E.Mul.check
local is_eadd   = E.Add.check
local is_ederef = E.DeRef.check


-------------------------------------------------------------------------------
-- Parsing from a Terra DSL
-------------------------------------------------------------------------------

-- example syntax:
--    local plop physical Triangles2 {
--      n_tri : uint32
--      _     : [4]byte
--      {
--        v : *[ti:n_tri][vi:3]uint32
--        n : *[ti:n_tri][ni:3]float64
--        c : *[ti:n_tri]float64
--      }
--    }

-- assumes physical tag and name have already been lexed out
local function terra_decl_parser(lexer)
  local parseDecl

  local function parseConst()
    local const = lexer:expect(lexer.number).value
    if not is_uint(const) or const <= 0 then
      lexer:error('expected positive integer')
    end
    return const
  end

  local function parseIdStr()
    local id = lexer:expect(lexer.name).value
    if not is_id_str(id) then
      lexer:error('expected valid identifier string') end
    return id
  end

  local function get_loc()
    -- linenumber, offset, filename
    return { lexer:cur().linenumber, lexer:cur().offset, lexer.source }
  end

  local function parsePrim()
    local loc = get_loc()
    local primname = lexer:expect(lexer.name).value
    local prim = string_to_primitive[primname]
    if not prim then
      lexer:error("primitive type name '"..primname.."' was unrecognized")
    end
    return A.DPrim(prim, unpack(loc))
  end


  local function parseRec()
    local loc  = get_loc()
    local name = parseIdStr()
    if lexer:nextif(':') then
      return A.Def( name, parseDecl(), unpack(loc) )
    else
      lexer:expect('=')
      if lexer:matches(lexer.number) then
        return A.Const( name, parseConst(), unpack(loc) )
      else
        local numerator, _, denominator = parseIdStr(),
                                          lexer:expect('/'),
                                          parseIdStr()
        return A.Chunk( name, numerator, denominator, unpack(loc) )
      end
    end
  end

  local function parseStruct()
    local loc = get_loc()
    local openline = lexer:expect('{').linenumber
    local recs = newlist()
    repeat
      recs:insert( parseRec() )
      -- skip optional comma or semicolon delimiters
      if      lexer:nextif(',') then
      elseif  lexer:nextif(';') then end
    until lexer:matches('}')
    lexer:expectmatch('}','{',openline)
    return A.Struct(recs, unpack(loc))
  end

  local function parsePtr()
    local loc = get_loc()
    lexer:expect('*')
    return A.Ptr(parseDecl(), unpack(loc))
  end

  local function parseArray()
    local loc = get_loc()
    local openline = lexer:expect('[').linenumber
    local sz_name, sz_val
    -- constant sugar
    if lexer:matches(lexer.number) then
      sz_val = parseConst()
    else
      sz_name = parseIdStr()
    end
    lexer:expectmatch(']','[',openline)
    return A.Array(sz_name,nil,sz_val, parseDecl(), unpack(loc))
  end

  function parseDecl()
    if      lexer:matches('[') then return parseArray()
    elseif  lexer:matches('*') then return parsePtr()
    elseif  lexer:matches('{') then return parseStruct()
                               else return parsePrim() end
  end

  local decl = parseStruct()
  return decl
end

-------------------------------------------------------------------------------
-- Programmatic Construction API
-------------------------------------------------------------------------------

local PreLayout   = {}
PreLayout.__index = PreLayout
local function is_pre_layout(obj) return getmetatable(obj) == PreLayout end
Exports.is_pre_layout = is_pre_layout

function NewPreDecl(decl)
  return setmetatable({ _hidden_decl=decl },PreLayout)
end
function NewPreRec(rec)
  return setmetatable({ _hidden_rec=rec },PreLayout)
end
local function is_pre_decl(obj)
  return is_pre_layout(obj) and obj._hidden_decl end
local function is_pre_rec(obj)
  return is_pre_layout(obj) and obj._hidden_rec end

-- to ensure the declarations form a tree proper
local null_loc = { 0, 0, 'no_src' }
local function clone_decl(decl)
  if      is_const(decl)  then
    return A.Const( decl.name, decl.val, unpack(null_loc) )
  elseif  is_chunk(decl)  then
    return A.Chunk( decl.name, decl.numerator,
                    decl.denominator, unpack(null_loc) )
  elseif  is_def(decl)    then
    return A.Def( decl.name, clone_decl(decl.typ), unpack(null_loc) )
  elseif  is_dprim(decl)  then
    return A.DPrim( decl.prim, unpack(null_loc) )
  elseif  is_ptr(decl)    then
    return A.Ptr( clone_decl(decl.typ), unpack(null_loc) )
  elseif  is_array(decl)    then
    return A.Array( decl.sizevar, decl.sizetype, decl.sizeval,
                    clone_decl(decl.typ), unpack(null_loc) )
  else -- is_struct(decl)    then
    return A.Struct( decl.entries:map(function(r) return clone_decl(r) end),
                     unpack(null_loc) )
  end
end

function Exports.ArrayOf(size, decl)
  local sizevar = is_id_str(size) and size or nil
  local sizeval = is_uint(size) and size or nil
  if not sizeval and not sizevar then
    error('first argument must be either a variable name or uint', 2)
  end
  if not is_pre_decl(decl) then
    error('second argument must be a type declaration', 2)
  end
  return NewPreDecl(A.Array(sizevar, nil, sizeval, decl._hidden_decl))
end
function Exports.PtrOf(decl)
  if not is_pre_decl(decl) then
    error('argument must be a type declaration', 2)
  end
  return NewPreDecl(A.Ptr(decl._hidden_decl))
end
function Exports.PrimOf(str)
  local prim = string_to_primitive[str]
  if not prim then
    error('did not recognize primitive type "'..tostring(str)..'"', 2)
  end
  return NewPreDecl(A.DPrim(prim))
end
function Exports.DefOf(name, decl)
  if not is_id_str(name) then
    error('first argument must be a variable name', 2)
  end
  if not is_pre_decl(decl) then
    error('second argument must be a type declaration', 2)
  end
  return NewPreRec(A.Def( name, decl._hidden_decl ))
end
function Exports.ConstOf(name, val)
  if not is_id_str(name) then
    error('first argument must be a variable name', 2)
  end
  if not is_uint(val) then
    error('second argument must be a uint', 2)
  end
  return NewPreRec(A.Const( name, val ))
end
function Exports.ChunkOf(name, numerator, denominator)
  if not is_id_str(name) then
    error('first argument must be a variable name', 2) end
  if not is_id_str(numerator) then
    error('second argument must be a variable name', 2) end
  if not is_id_str(denominator) then
    error('third argument must be a variable name', 2) end
  return NewPreRec(A.Chunk( name, numerator, denominator ))
end
function Exports.StructOf(...)
  local entries = newlist()
  for i=1,select('#',...) do
    local rec = select(i,...)
    if not is_pre_rec(rec) then
      error('argument #'..i..' was not a struct entry', 2)
    end
    entries:insert(rec._hidden_rec)
  end
  return NewPreDecl(A.Struct(entries))
end

-------------------------------------------------------------------------------
-- Path Normalization
-------------------------------------------------------------------------------

local function insert_raw_name(xs, x)
  xs:insert( tostring(x) )
end
function P.Path:normalized_seqs()
  if self._norm_faseq then return self._norm_faseq, self._norm_aiseq end

  local faseq, aiseq = newlist(), newlist()
  for _,tkn in ipairs(self.tokens) do
    if      P.Field.check(tkn) then insert_raw_name(faseq, tkn.name)
    elseif  P.Index.check(tkn) then insert_raw_name(aiseq, tkn.name)
    end
  end
  table.sort(faseq)
  table.sort(aiseq)
  self._norm_faseq, self._norm_aiseq = memolist(faseq), memolist(aiseq)
  return self._norm_faseq, self._norm_aiseq
end
function P.Path:normalized_key() -- key for normalized seq.
  if self._norm_key then return self._norm_key end
  self._norm_key = memolist({ self:normalized_seqs() })
  return self._norm_key
end

function P.Path:subpathof(rhs)
  local fa1, ai1 = self:normalized_seqs()
  local fa2, ai2 = rhs:normalized_seqs()
  -- is fa1 a subseq of fa2?
  --print('fa1', unpack(fa1))
  --print('fa2', unpack(fa2))
  local i1,i2 = 1,1
  while i1 <= #fa1 and i2 <= #fa2 do
    if fa1[i1] == fa2[i2] then i1 = i1 + 1 end
    i2 = i2 + 1
  end
  --print('','decide', i1,i2, not(i1 <= #fa1))
  if i1 <= #fa1 then return false end
  -- and is ai1 a subseq of ai2
  --i1,i2 = 1,1
  --while i1 <= #ai1 and i2 <= #ai2 do
  --  if ai1[i1] == ai2[i2] then i1 = i1 + 1 end
  --  i2 = i2 + 1
  --end
  --if i1 <= #ai1 then return false end
  return true
end




local function incr_set_count(set,key)
  local val = set[key] or 0
  set[key] = val + 1
end

function P.Path:normalized_sets()
  if self._fa_norm_set then return self._fa_norm_set, self._ai_norm_set end
  local faset, aiset = {}, {}
  for _,tkn in ipairs(self.tokens) do
    if      P.Field.check(tkn) then incr_set_count(faset, tkn.name)
    elseif  P.Index.check(tkn) then incr_set_count(aiset, tkn.name) end
  end
  self._fa_norm_set, self._ai_norm_set = faset, aiset
  return faset, aiset
end

-------------------------------------------------------------------------------
-- Path Sets (built by the typechecking pass)
-------------------------------------------------------------------------------

-- holds PathSet objects keyed on A.Decl objects
local allpaths_weak_cache = setmetatable({},{__mode = "k"})
local varpaths_weak_cache = setmetatable({},{__mode = "k"})

local PathSet = {}
PathSet.__index = PathSet
local function newPathSet()
  return setmetatable({ paths={} },PathSet)
end
function PathSet:prepend(token)
  local set = newPathSet()
  for path,_ in pairs(self.paths) do
    local newpath = P.Path( newlist{ token, unpack(path.tokens) },
                            path.terminal )
    set.paths[newpath] = true
  end
  return set
end
function PathSet:addpath(sym, terminal)
  local tkns = sym and newlist{ P.Field(sym) } or newlist()
  self.paths[P.Path(tkns, terminal)] = true
end
function PathSet:addpaths(set)
  for path,_ in pairs(set.paths) do self.paths[path] = true end
end

function PathSet:is_ambiguous()
  -- this could be substantially more efficient...
  for p1,_ in pairs(self.paths) do
    for p2,_ in pairs(self.paths) do
      if p1 ~= p2 and p1:subpathof(p2) then
        return true, "The path "..tostring(p1).." is a sub-path of "..
                     tostring(p2)..", meaning that if the paths are "..
                     "re-ordered, then there could be an ambiguity "..
                     "about whether data or a sub-structure is being "..
                     "referred to."
      end
    end
  end
  return false
end


-------------------------------------------------------------------------------
-- Logical Sub-Typing of Decls
-------------------------------------------------------------------------------

-- returns a set keyed by normalized path-sequence objects
local weak_norm_path_cache = setmetatable({},{__mode = "k"})
local function normalized_paths(decl)
--function A.Decl:normalized_paths()
  if weak_norm_path_cache[decl] then return weak_norm_path_cache[decl] end
  local nkp = {}
  for path,_ in pairs(allpaths_weak_cache[decl].paths) do
    local normkey = path:normalized_key()
    nkp[normkey] = path
  end
  weak_norm_path_cache[decl] = nkp
  return nkp
end

local prim_supertype_table = {
  [ A.SIZE   ] = A.SIZE,
  [ A.UINT   ] = A.UINT,
  [ A.INT    ] = A.INT,
  [ A.BOOL   ] = A.BOOL,
  [ A.FLOAT  ] = A.FLOAT,
  [ A.SIZE8  ] = A.SIZE,
  [ A.SIZE16 ] = A.SIZE,
  [ A.SIZE32 ] = A.SIZE,
  [ A.SIZE64 ] = A.SIZE,
  [ A.UINT8  ] = A.UINT,
  [ A.UINT16 ] = A.UINT,
  [ A.UINT32 ] = A.UINT,
  [ A.UINT64 ] = A.UINT,
  [ A.INT8   ] = A.INT,
  [ A.INT16  ] = A.INT,
  [ A.INT32  ] = A.INT,
  [ A.INT64  ] = A.INT,
  [ A.FLOAT32] = A.FLOAT,
  [ A.FLOAT64] = A.FLOAT,
}
local function prim_subtype(lhp, rhp)
  return lhp == rhp -- simple case
      or prim_supertype_table[lhp] == rhp
      or (rhp == A.BOOL and prim_supertype_table[lhp] == A.UINT)
end
local function terminal_subtype(lpath, rpath)
  local lht, rht = lpath.terminal, rpath.terminal
  local lnum = type(lht) == 'number' and lht
  local rnum = type(rht) == 'number' and rht
  if lnum then
    if rnum then return lnum == rnum end
    -- otherwise, does this number fit in the specified bits?
    local bd = size_num_bound_table[rht]
    return bd and lnum < bd
  else
    if rnum then return false end
    return prim_subtype(lht, rht) 
  end
end

function A.Decl:logical_subtype_of(rhdecl)
  local lhdecl = self
  -- true if the set of normalized paths on the right is a subset of
  -- the normalized paths on the left.
  -- WITH the added caveat that the terminals must be subtypes
  local lNP = normalized_paths(lhdecl)
  local rNP = normalized_paths(rhdecl)
  for k,rpath in pairs(rNP) do
    local lpath = lNP[k]
    if not lpath or not terminal_subtype(lpath, rpath) then return false end
  end
  return true
end

function A.Decl:logical_equal_of(rhdecl)
  local lhdecl = self
  -- true if the set of normalized paths on the right is the same as
  -- the normalized paths on the left.
  -- WITH the added caveat that the terminals must match exactly
  local lNP = normalized_paths(lhdecl)
  local rNP = normalized_paths(rhdecl)
  for k,lpath in pairs(lNP) do -- check inclusion one way
    if not rNP[k] then return false end
  end
  for k,rpath in pairs(rNP) do -- check inclusion and prim match the other
    local lpath = lNP[k]
    if not lpath or lpath.terminal ~= rpath.terminal then return false end
  end
  return true
end


-------------------------------------------------------------------------------
-- Typechecking
-------------------------------------------------------------------------------
-- Typechecking ensures that names don't alias improperly, are in scope,
-- and are well-defined.
-- Typechecking also extracts useful information in the form of paths.

local TypingContext   = {}
TypingContext.__index = TypingContext

local function new_typing_context()
  return setmetatable({
    _env        = terralib.newenvironment(),
    _var_defs   = {},
    _diag       = terralib.newdiagnostics(),
  }, TypingContext)
end

function TypingContext:env()        return self._env:localenv() end
function TypingContext:pushscope()  self._env:enterblock()      end
function TypingContext:popscope()   self._env:leaveblock()      end
function TypingContext:error(node, ...)
  self._diag:reporterror(node, ...)
end

function TypingContext:begin()
end
function TypingContext:finish(decl,depth)
  depth = depth or 1
  if self._diag:haserrors() and decl.filename == 'no_src' then
    print('This Layout had typing errors')
    print(decl)
  end
  self._diag:finishandabortiferrors(
    "Errors found in plop definition", depth+1)
end

local typechecking_pass

local max_int32_val = math.pow(2,31)-1
--function A.Array:typecheck(ctxt)
local function typechecking_array(self, ctxt)
  -- determine type and or const value
  if self.sizeval then -- had a constant annotation
    -- append an identifier distinguishing successive array lookups
    local lookup  = ctxt:env()[self.sizeval]
    lookup        = lookup and (lookup+1) or 0
    self.sizevar  = tostring(self.sizeval)..'_'..lookup
    ctxt:env()[self.sizeval] = lookup

    self.sizetype = (self.sizeval < max_int32_val) and A.SIZE32 or A.SIZE64
  else
    local symname = tostring(self.sizevar)
    local lookup  = ctxt:env()[symname]
    if not lookup or lookup.errtyp then
      if lookup and lookup.errtyp then
        ctxt:error(self,"tried to use variable '"..tostring(self.sizevar)..
                        "', which has type "..tostring(lookup.errtyp)..
                        ".  Did you mean to give it size type?")
      else
        ctxt:error(self,"variable '"..tostring(self.sizevar)..
                        "' used here was undefined.")
      end
    else
      self.sizevar    = lookup.sym
      self.sizeval    = lookup.val -- one of these will be nil
      self.sizetype   = lookup.typ -- one of these will be nil
      self.size_num   = lookup.numerator
      self.size_denom = lookup.denominator
    end
  end

  local vars, paths = typechecking_pass( self.typ, ctxt )
  return vars:prepend(P.Index(self.sizevar)),
         paths:prepend(P.Index(self.sizevar))
end

--function A.Struct:typecheck(ctxt)
local function typechecking_struct(self, ctxt)
  local varpaths, allpaths = newPathSet(), newPathSet()

  ctxt:pushscope()
  self._lookup_fields = {}
  local function addlookup(name,idx,rec)
    if self._lookup_fields[name] then
      ctxt:error(rec,"cannot have two entries with the same name: '"..
                     name.."'") end
    self._lookup_fields[name] = idx
  end
  for i_rec,rec in ipairs(self.entries) do
    local namestr = tostring(rec.name)
    if is_const(rec) then
      if namestr == '_' then
        ctxt:error(self,"cannot assign a constant value to "..
                        "the special no-name character '_'")
      end
      addlookup(namestr, i_rec, rec)
      ctxt:env()[namestr] = { sym=rec.name, val=rec.val }
      --local size_typ = size_bound_of_num(rec.val)
      allpaths:addpath(rec.name, rec.val)
    elseif is_chunk(rec) then
      if namestr == '_' then
        ctxt:error(self,"cannot assign a chunked value to "..
                        "the special no-name character '_'")
      end
      local env = ctxt:env()
      local num, denom = rec.numerator, rec.denominator
      local numrec, denomrec = env[num], env[denom]
      if not denomrec or not denomrec.val then
        ctxt:error(self,"denominator in chunked expression must be "..
                        "a constant variable") end
      if not numrec or not numrec.typ then
        ctxt:error(self,"numerator in chunked expression must be "..
                        "a size variable")
      else
        addlookup(namestr, i_rec, rec)
        env[namestr] = { sym=rec.name, typ = numrec.typ,
                         numerator=num, denominator=denomrec.val }
        allpaths:addpath(rec.name, numrec.typ)
      end
    else -- A.Def
      if is_dprim(rec.typ) then
        -- add all variables to the allpaths; only size variables
        -- to the variable store
        if namestr ~= '_' then
          addlookup(namestr, i_rec, rec)
          allpaths:addpath(rec.name, rec.typ.prim)
        end
        if is_size_prim(rec.typ.prim) then
          ctxt:env()[namestr] = { sym=rec.name, typ=rec.typ.prim }
          varpaths:addpath(rec.name, rec.typ.prim)
        else
          ctxt:env()[namestr] = { errtyp=rec.typ.prim }
        end
      else
        local vars, paths = typechecking_pass(rec.typ, ctxt)
        if namestr ~= '_' then
          addlookup(namestr, i_rec, rec)
          allpaths:addpaths( paths:prepend(P.Field(rec.name)) )
        end
        varpaths:addpaths( vars:prepend(P.Field(rec.name)) )
      end
    end
  end
  ctxt:popscope()

  return varpaths, allpaths
end

function typechecking_pass(decl, ctxt)
  local varpaths, allpaths

  if is_dprim(decl) then
    varpaths = newPathSet()
    allpaths = newPathSet()
    allpaths:addpath(nil,decl.prim)
  elseif is_ptr(decl) then
    local vars, paths = typechecking_pass(decl.typ, ctxt)
    allpaths          = paths:prepend(P.DeRef)
    varpaths          = vars:prepend(P.DeRef)
  elseif is_array(decl) then
    varpaths, allpaths = typechecking_array(decl, ctxt)
  else --is_struct(decl) then
    varpaths, allpaths = typechecking_struct(decl, ctxt)
  end

  varpaths_weak_cache[decl] = varpaths
  allpaths_weak_cache[decl] = allpaths
  return varpaths, allpaths
end

local function typecheck_decl(decl)
  local ctxt = new_typing_context()

  ctxt:begin()
  typechecking_pass(decl,ctxt) --decl:typecheck(ctxt)
  ctxt:finish(decl,3)

  local is_err, errmsg = allpaths_weak_cache[decl]:is_ambiguous()
  if is_err then
    error('This plop definition contains ambiguous paths\n'..errmsg, 3)
  end

  return decl
end

function A.Struct:find_entry(name)
  return self._lookup_fields[name]
end

-------------------------------------------------------------------------------
-- Logical vs. Physical Layouts
-------------------------------------------------------------------------------

do
  -- lattice values (logical, physical, top, bottom)
  local L,P, T,B = {},{},{},{}
  local lp_meet = {
    [T]={ [T] = T,  [L] = L,  [P] = P,  [B] = B },
    [L]={ [T] = L,  [L] = L,  [P] = B,  [B] = B },
    [P]={ [T] = P,  [L] = B,  [P] = P,  [B] = B },
    [B]={ [T] = B,  [L] = B,  [P] = B,  [B] = B },
  }

  local lp_weak_cache = setmetatable({},{__mode = "k"})
  local function lp_analysis(decl)
    if lp_weak_cache[decl] then return lp_weak_cache[decl] end
    local lp = T

    if      is_dprim(decl)  then
      lp = physical_prim_table[decl.prim] and T or L
    elseif  is_array(decl)  then
      lp = lp_analysis(decl.typ)
    elseif  is_struct(decl) then
      for _,rec in ipairs(decl.entries) do if rec.typ then
        lp = lp_meet[lp][lp_analysis(rec.typ)]
      end end
    else -- is ptr
      lp = P
    end

    lp_weak_cache[decl] = lp
    return lp
  end

  function A.Decl:is_physical()
    local lp = lp_analysis(self)
    return lp == P or lp == T
  end
  function A.Decl:is_logical()
    local lp = lp_analysis(self)
    return lp == L or lp == T
  end
end

-------------------------------------------------------------------------------
-- Expression Implementation
-------------------------------------------------------------------------------

function E.Expr.__add(lhs, rhs)
  assert(E.Expr.check(rhs), 'right-hand-side to expression addition '..
                            'must be an expression')
  local lconst, rconst = 0,0
  local exprs = newlist()

  if E.Const.check(lhs) then
    lconst = lhs.val
  elseif E.Add.check(lhs) then
    lconst = lhs.const
    exprs:insertall(lhs.exprs)
  else
    exprs:insert(lhs)
  end
  if E.Const.check(rhs) then
    rconst = rhs.val
  elseif E.Add.check(rhs) then
    rconst = rhs.const
    exprs:insertall(rhs.exprs)
  else
    exprs:insert(rhs)
  end

  if #exprs > 0 then
    return NewE.Add(lconst + rconst, exprs)
  else -- all constant values
    return NewE.Const(lconst + rconst)
  end
end

function E.Expr.__mul(lhs, rhs)
  assert(E.Expr.check(rhs), 'right-hand-side to expression multiplication '..
                            'must be an expression')
  local lconst, rconst = 1,1
  local exprs = newlist()

  if E.Const.check(lhs) then
    lconst = lhs.val
  elseif E.Add.check(lhs) then
    lconst = lhs.const
    exprs:insertall(lhs.exprs)
  else
    exprs:insert(lhs)
  end
  if E.Const.check(rhs) then
    rconst = rhs.val
  elseif E.Add.check(rhs) then
    rconst = rhs.const
    exprs:insertall(rhs.exprs)
  else
    exprs:insert(rhs)
  end

  local c = lconst * rconst
  if c == 0 then -- multiplication by zero cancels out everything
    return NewE.Const(0)
  elseif #exprs > 0 then
    return NewE.Mul(c, exprs)
  else
    return NewE.Const(c)
  end
end

function E.Expr:deref(prim)
  return NewE.DeRef(self, prim)
end

-------------------------------------------------------------------------------
-- SizeOf
-------------------------------------------------------------------------------

local pointer_size    = NewE.Const(8)
local primitive_sizes = {
  [ A.SIZE8 ]     = NewE.Const(1),
  [ A.SIZE16 ]    = NewE.Const(2),
  [ A.SIZE32 ]    = NewE.Const(4),
  [ A.SIZE64 ]    = NewE.Const(8),
  [ A.UINT8 ]     = NewE.Const(1),
  [ A.UINT16 ]    = NewE.Const(2),
  [ A.UINT32 ]    = NewE.Const(4),
  [ A.UINT64 ]    = NewE.Const(8),
  [ A.INT8 ]      = NewE.Const(1),
  [ A.INT16 ]     = NewE.Const(2),
  [ A.INT32 ]     = NewE.Const(4),
  [ A.INT64 ]     = NewE.Const(8),
  [ A.FLOAT32 ]   = NewE.Const(4),
  [ A.FLOAT64 ]   = NewE.Const(8),
}

-------------------------------------------------------------------------------
-- Environment-Based SizeOf and Offset
-------------------------------------------------------------------------------

local Recursive_Environment   = {}
Recursive_Environment.__index = Recursive_Environment

local function New_Recursive_Environment()
  return setmetatable({
    _vars = {},
    _errs = newlist(),
  }, Recursive_Environment)
end

function Recursive_Environment:lookup(var_id,typ)
  local val = self._vars[var_id]
  if val then
    return val
  else
    self._errs:insert("failed to lookup '"..var_id.."'")
    return NewE.Var(var_id,typ) -- dummy value
  end
end
function Recursive_Environment:bind(var_id, expr)
  self._vars[var_id] = expr
end
function Recursive_Environment:haserrors() return #self._errs > 0 end
function Recursive_Environment:geterrors() return self._errs end
function Recursive_Environment:pushenv()
  local prev_vars = self._vars
  self._vars      = setmetatable({},{ __index=prev_vars })
end
function Recursive_Environment:popenv()
  self._vars      = getmetatable(self._vars).__index
end

local function const_size(decl,env) -- returns Expr
  if      is_prim(decl)   then return primitive_sizes[decl]
  elseif  is_dprim(decl)  then return primitive_sizes[decl.prim]
  elseif  is_ptr(decl)    then return pointer_size
  elseif  is_array(decl)  then
    local n_elems = (decl.sizeval and NewE.Const(decl.sizeval)
                                   or env:lookup(decl.sizevar,decl.sizetype))
    return n_elems * const_size(decl.typ,env)
  elseif  is_struct(decl) then
    local sz = NewE.Const(0)
    for _,rec in ipairs(decl.entries) do if is_def(rec) then
      sz = sz + const_size(rec.typ,env)
    end end
    return sz
  end
end

-- returns the size of the declaration, with the capability of reading
-- data and extending the environment appropriately.
local function offsize(decl,env,ptr) -- returns Expr
  if is_struct(decl) then
    local sz = NewE.Const(0)
    env:pushenv()
    for _,rec in ipairs(decl.entries) do
      if is_def(rec) then
        if is_dprim(rec.typ) and is_size_prim(rec.typ.prim) then
          env:bind( rec.name, ptr:deref(rec.typ.prim) )
        end
        local s = offsize(rec.typ, env, ptr)
        ptr = ptr + s
        sz  = sz  + s
      end
      --elseif is_const(rec) then
      --  env:bind(rec.name, NewE.Const(rec.val))
      --end
    end
    env:popenv()
    return sz
  else
    return const_size(decl,env)
  end
end

local offpath_err = 'invalid path arg to offset'
local function pathoff(decl, env, ptr, ...)
  if select('#',...) == 0 then return ptr end

  if is_struct(decl) then
    local f_name = assert(select(1,...).name, offpath_err)
    env:pushenv()
    for _,rec in ipairs(decl.entries) do
      if is_def(rec) then
        if rec.name == f_name then
          return pathoff(rec.typ, env, ptr, select(2,...))
        elseif is_dprim(rec.typ) and is_size_prim(rec.typ.prim) then
          env:bind( rec.name, ptr:deref(rec.typ.prim) )
        end
        ptr = ptr + offsize(rec.typ, env, ptr)
      end
      --elseif is_const(rec) then
      --  env:bind(rec.name, NewE.Const(rec.val))
      --end
    end
    assert(false, offpath_err)
  elseif is_array(decl) then
    local idxvar = select(1,...).name
    assert(idxvar == decl.sizevar, offpath_err)
    return pathoff( decl.typ, env,
                    ptr + NewE.Idx(idxvar) * const_size(decl.typ, env),
                    select(2,...) )
  elseif is_ptr(decl) then -- is ptr
    assert(P.DeRef.check(select(1,...)), offpath_err)
    return pathoff( decl.typ, env, ptr:deref(), select(2,...) )
  else
    assert(false, offpath_err)
  end
end

-- returns nil when failures
local function const_sizeof_decl(decl)
  local env   = New_Recursive_Environment()
  local size  = const_size(decl,env)
  if env:haserrors() then return nil else return size end
end

-- returns the expression with variables in place of failed lookups
local function sizeof_expr(decl)
  return const_size(decl, New_Recursive_Environment())
end


-------------------------------------------------------------------------------
-- Random Access Analysis
-------------------------------------------------------------------------------

--local rand_access_check_interp = {
--  deref     = function(x, prim) end,
--  add       = function(x,y) end,
--  mul       = function(x,y) end,
--  const     = function(n) end,
--  default   = function() end,
--  ptr       = function() end,
--  variable  = function(name) end,
--  idxvar    = function(name) end,
--}
local function is_path_random_access(decl, path_tokens)
  local env = New_Recursive_Environment()
  pathoff( decl, env, NewE.Const(0), unpack(path_tokens) )
  if env:haserrors() then return false, env:geterrors() end
  return true
end

local function get_paths_to_check(decl, paths)
  for p,_ in pairs(varpaths_weak_cache[decl].paths) do
    assert(is_size_prim(p.terminal))
    paths:insert( p.tokens )
  end
end

local rand_access_weak_cache = setmetatable({},{__mode = "k"})
for _,prim in pairs(all_primitives) do rand_access_weak_cache[prim] = true end
local function is_random_access(decl)
  if rand_access_weak_cache[decl] then return true end

  local paths = newlist()
  get_paths_to_check(decl, paths)

  for _,tkns in ipairs(paths) do
    local status, errs = is_path_random_access(decl, tkns)
    if not status then return status, errs end
  end
  
  rand_access_weak_cache[decl] = true
  return true
end

-------------------------------------------------------------------------------
-- Alignment Analysis
-------------------------------------------------------------------------------

local function alignment(decl)
  if      is_def(decl) or is_array(decl)  then 
    return alignment(decl.typ)
  elseif  is_dprim(decl) or is_ptr(decl)  then 
    return const_sizeof_decl(decl).val
  elseif  is_const(decl)  then
    return 0
  elseif  is_struct(decl) then
    local a = 0
    for _,r in ipairs(decl.entries) do  a = math.max(a, alignment(r)) end
    return a
  end
end

-- need to be able to compute the largest divisor that is a power of 2...
-- this is not a precise analysis, but if we already ran
-- constant propagation, it's pretty good.  That can be formalized?
local function g2d_of_num(n)
  if n == 0 then return math.huge end -- everything divides 0
  local d = 1; while n%2 == 0 do d=2*d; n=n/2 end
  return d
end
--function E.Const:g2d()  return g2d_of_num(self.val)  end
local function g2d(e)
  if      is_econst(e)  then  return g2d_of_num(e.val)
  elseif  is_evar(e)    then  return 1
  elseif  is_ederef(e)  then  return math.huge
  elseif  is_emul(e)    then
    local val = e.const
    for _,sub in ipairs(e.exprs) do val = val * g2d(sub) end
    return val
  else -- is add
    local val = (e.const == 0) and math.huge or e.const
    for _,sub in ipairs(e.exprs) do val = math.min( val, g2d(sub) ) end
    return val
  end
end

-- then the following logic is patterned off of offset() and checks
-- whether or not a declaration is aligned
local function align_err(decl, req, actual)
  local extra_info = ""
  if decl.filename == 'no_src' then
    extra_info = '\n'..tostring(decl)
  end
  local errstr = string.format(
    'found invalid alignment at %s:%d\n'..
    '  required alignment is %d bytes\n'..
    '  but, is only guaranteed to align to %d bytes'..extra_info,
    decl.filename, decl.linenumber, req, actual )
  return false, errstr
end

local function is_aligned(decl, addr)
  if is_struct(decl) then
    addr = addr or NewE.Const(0)
    for _,rec in ipairs(decl.entries) do
      if rec.typ then
        local a, d = alignment(rec.typ), g2d(addr)
        if a > d then return align_err(rec, a,d) end
        local status, err = is_aligned( rec.typ, addr )
        if not status then return status, err end
        addr = addr + sizeof_expr(rec.typ)
      end
    end
    return true
  else
    local a,d = alignment(decl), g2d(addr)
    if a > d then return align_err(decl, a,d) end
    if      is_dprim(decl) then return true
    elseif  is_ptr(decl) then return is_aligned( decl.typ, addr:deref() )
    else -- array
      local xd = g2d( sizeof_expr(decl.typ) )
      if a > xd then return align_err(decl,a,xd)
      else return is_aligned( decl.typ,
        addr + sizeof_expr(decl.typ) * NewE.Var(decl.sizevar, decl.sizetype)
      ) end
    end
  end
end



-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Layout Wrappers (for exposing functionality)
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

local LayoutWrapper   = {}
LayoutWrapper.__index = LayoutWrapper
local PhysicalWrapper   = setmetatable({},LayoutWrapper)
PhysicalWrapper.__index = PhysicalWrapper
local LogicalWrapper    = setmetatable({},LayoutWrapper)
LogicalWrapper.__index  = LogicalWrapper
local PrimitiveWrapper    = setmetatable({},LayoutWrapper)
PrimitiveWrapper.__index  = PrimitiveWrapper

local is_ptr_decl     = is_ptr
local is_array_decl   = is_array
local is_struct_decl  = is_struct
local is_prim_decl    = is_prim
local is_size_prim_decl = is_size_prim

local function is_layout(obj)
  return getmetatable(getmetatable(obj)) == LayoutWrapper
end
local function is_prim(obj)
  return getmetatable(obj) == PrimitiveWrapper
end
local function is_size_prim(obj)
  return is_prim(obj) and is_size_prim_decl(obj._decl)
end
local function is_physical(obj)
  return (is_prim(obj) and is_phys_prim(obj._decl))
      or getmetatable(obj) == PhysicalWrapper
end
local function is_logical(obj)
  return is_prim(obj) or getmetatable(obj) == LogicalWrapper
end
local function is_ptr(obj)
  return is_layout(obj) and is_ptr_decl(obj._decl)
end
local function is_array(obj)
  return is_layout(obj) and is_array_decl(obj._decl)
end
local function is_struct(obj)
  return is_layout(obj) and is_struct_decl(obj._decl)
end
LayoutWrapper.is_physical   = is_physical
LayoutWrapper.is_logical    = is_logical
LayoutWrapper.is_prim       = is_prim
LayoutWrapper.is_size_prim  = is_size_prim
LayoutWrapper.is_ptr        = is_ptr
LayoutWrapper.is_array      = is_array
LayoutWrapper.is_struct     = is_struct

Exports.is_layout     = is_layout
Exports.is_physical   = is_physical
Exports.is_logical    = is_logical
Exports.is_prim       = is_prim
Exports.is_size_prim  = is_size_prim
Exports.is_ptr        = is_ptr
Exports.is_array      = is_array
Exports.is_struct     = is_struct

local primitive_wrappers = {}
for name,p in pairs(string_to_primitive) do
  local pwrap = primitive_wrappers[p]
  if not pwrap then
    pwrap = setmetatable({ _name = name, _decl = p }, PrimitiveWrapper)
    primitive_wrappers[p] = pwrap
  end
  Exports[name] = pwrap
end
primitive_wrappers[A.UINT8]._name = 'uint8'

function LogicalWrapper:__tostring()    return self._decl:prettystr() end
function PrimitiveWrapper:__tostring()  return tostring(self._decl)   end
PhysicalWrapper.__tostring = LogicalWrapper.__tostring

function LayoutWrapper:deref()
  if not self:is_ptr() then
    error('can only call deref() on pointer layouts', 2)
  end
  return self._decl.typ._wrapper -- sub-wrapper
end
function LayoutWrapper:arrayvar()
  if not self:is_array() then
    error('may only call arraysize() on an array', 2) end
  return public_sym_convert(self._decl.sizevar)
end
function LayoutWrapper:arraysize()
  if not self:is_array() then
    error('may only call arraysize() on an array', 2) end
  return self._decl.sizeval
end
function LayoutWrapper:arraysizetype()
  if not self:is_array() then
    error('may only call arraysizetype() on an array', 2) end
  return public_prim_convert(self._decl.sizetype)
end
function LayoutWrapper:arrayelem()
  if not self:is_array() then
    error('may only call arrayelem() on an array', 2) end
  return self._decl.typ._wrapper
end
local field_list_weak_cache = setmetatable({},{__mode='k'})
function LayoutWrapper:fields()
  if not self:is_struct() then
    error('may only call fields() on a struct', 2) end
  if field_list_weak_cache[self] then return field_list_weak_cache[self]
  else
    local fs = newlist()
    field_list_weak_cache[self] = fs
    for _,rec in ipairs(self._decl.entries) do
      fs:insert { name=rec.name,
                  typ=rec.typ and rec.typ._wrapper,
                  val=rec.val }
    end
    return fs
  end
end
function LayoutWrapper:findfield(name)
  return self._decl:find_entry(name)
end


function LayoutWrapper:subtype_of(rhwrap)
  if not is_layout(rhwrap) then error('expected layout as argument', 2) end
  return self._decl:logical_subtype_of(rhwrap._decl)
end
function LayoutWrapper:equals(rhwrap)
  if not is_layout(rhwrap) then error('expected layout as argument', 2) end
  return self._decl:logical_equal_of(rhwrap._decl)
end

function LayoutWrapper:name() return self._name end






-- PRE-DECLARATIONS of extension installation functions
local run_extensions_on_declaration, run_extensions_on_specialization

local wrap_counter = 0
local function new_layout_wrapper(name, decl, physical_flag)
  if is_dprim(decl) then
    local wrap      = primitive_wrappers[decl.prim]
    decl._wrapper   = wrap
    return wrap
  else
    wrap_counter = wrap_counter+1
    name = name or '_'..tostring(wrap_counter)

    -- create wrappers for child decl
    if  A.Ptr.check(decl) then
      new_layout_wrapper(name..'_p', decl.typ, physical_flag)
    elseif  A.Array.check(decl) then
      new_layout_wrapper(name..'_'..tostring(decl.sizevar),
                         decl.typ, physical_flag)
    elseif  A.Struct.check(decl) then
      for _,rec in ipairs(decl.entries) do
        if rec.typ then
          new_layout_wrapper(name..'_'..tostring(rec.name),
                             rec.typ, physical_flag)
        end
      end
    end

    local wrap = setmetatable({
      _name       = name,
      _decl       = decl,
    }, physical_flag and PhysicalWrapper or LogicalWrapper)
    decl._wrapper = wrap
    -- extension stack
    run_extensions_on_declaration(wrap)

    return wrap
  end
end


local function wrap_physical(decl, name)
  if not decl:is_physical() then
    error('Declaration was not a physical declaration.  '..
          'Physical declarations must specify the number of bits '..
          'in all their primitive types', 3)
  end

  -- check alignment
  local status, errmsg = is_aligned(decl)
  if not status then
    error(errmsg, 3)
  end

  -- check random-access
  local status, errs = is_random_access(decl)
  if not status then
    if decl.filename == 'no_src' then
      print('The following layout has random access errors')
      print(decl)
    end
    error("This plop definition is not randomly accessible\n"..
          "The following size variables recursively depend on their "..
          "own value in order to determine their location:\n"..
          errs:map(function(vn) return '  '..tostring(vn) end):concat('\n'),
          3)
  end

  -- wrap this up
  return new_layout_wrapper(name, decl, true) -- yes, is physical
end

local function wrap_logical(decl, name)
  if not decl:is_logical() then
    error('Declaration was not a logical declaration.  '..
          'Logical declarations may not use pointers', 3)
  end

  -- wrap this up
  return new_layout_wrapper(name, decl, false) -- no, is not physical
end

-- for the programmatic interface
function PreLayout:compile_physical(name)
  if not self._hidden_decl or not A.Struct.check(self._hidden_decl) then
    error('can only compile struct layouts', 2)
  end
  local decl = clone_decl(self._hidden_decl)
  typecheck_decl(decl)
  return wrap_physical(decl, name)
end
function PreLayout:compile_logical(name)
  if not self._hidden_decl or not A.Struct.check(self._hidden_decl) then
    error('can only compile struct layouts', 2)
  end
  local decl = clone_decl(self._hidden_decl)
  typecheck_decl(decl)
  return wrap_logical(decl, name)
end


function LogicalWrapper:is_specialized()
  return self._physical_layout ~= nil
end
function LogicalWrapper:physical_layout()
  return self._physical_layout
end
function LogicalWrapper:__call(phys_layout)
  if not is_physical(phys_layout) then
    error('logical layouts may only be specialized using physical layouts', 2)
  end
  if self:is_specialized() then
    error('this logical layout is already specialized', 2)
  end
  if not phys_layout:subtype_of(self) then
    error('provided physical type was not a logical sub-type, '..
          'so cannot specialize on it', 2)
  end

  -- could use a better base name...
  local base_name = self._name..'_'..phys_layout._name
  local wrap = setmetatable({
    _name             = base_name,
    _decl             = self._decl,
    _physical_layout  = phys_layout,
  }, LogicalWrapper)

  run_extensions_on_specialization(wrap)

  return wrap
end



function PrimitiveWrapper:terra_prim() return self._decl:toterratyp() end
function LayoutWrapper:terra_prim() return nil end

function A.SIZE8:toterratyp()     return uint8  end
function A.SIZE16:toterratyp()    return uint16 end
function A.SIZE32:toterratyp()    return uint32 end
function A.SIZE64:toterratyp()    return uint64 end
function A.UINT8:toterratyp()     return uint8  end
function A.UINT16:toterratyp()    return uint16 end
function A.UINT32:toterratyp()    return uint32 end
function A.UINT64:toterratyp()    return uint64 end
function A.INT8:toterratyp()      return int8   end
function A.INT16:toterratyp()     return int16  end
function A.INT32:toterratyp()     return int32  end
function A.INT64:toterratyp()     return int64  end
function A.FLOAT32:toterratyp()   return float  end
function A.FLOAT64:toterratyp()   return double end


-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Extensions
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

local plop_extension_stack = newlist()

local Extension   = {}
Extension.__index = Extension
local function is_extension(obj) return getmetatable(obj) == Extension end


local function new_extension(args)
  if type(args.name) ~= 'string' then
    error('must provide extension name', 2) end
  if type(args.at_init) ~= 'function' then
    error("must provide 'at_init' function", 2) end
  if type(args.at_declaration) ~= 'function' then
    error("must provide 'at_declaration' function", 2) end
  if type(args.at_specialization) ~= 'function' then
    error("must provide 'at_specialization' function", 2) end
  return setmetatable({
    name                = args.name,
    at_init             = args.at_init, -- gets passed primitives
    at_declaration      = args.at_declaration, -- per plop declaration
    at_specialization   = args.at_specialization, -- per specialization
  }, Extension)
end

local prim_wrap_list = newlist()
for _,pwrap in pairs(primitive_wrappers) do prim_wrap_list:insert(pwrap) end
local function add_extensions(arg)
  local exts = {}
  if is_extension(arg) then 
    exts = {arg}
  else
    if not terralib.israwlist(arg) then
      error('expected plop extension or list of extensions as argument', 2)
    end
    for i,e in ipairs(arg) do
      if not is_extension(e) then
        error('entry #'..i..' was not an extension', 2)
      else
        exts[i] = e
    end end
  end

  for i,ext in ipairs(exts) do
    plop_extension_stack:insert(ext)
    ext.at_init {
      primitives      = prim_wrap_list,
      layout_proto    = LayoutWrapper,
      physical_proto  = PhysicalWrapper,
      logical_proto   = LogicalWrapper,
    }
  end
end

-- run_extensions_on_declaration and run_extensions_on_specialization
-- are both pre-declared functions
function run_extensions_on_declaration(wrapper)
  -- primitives
  for _,ext in ipairs(plop_extension_stack) do
    ext.at_declaration(wrapper)
  end
end
function run_extensions_on_specialization(wrapper)
  for _,ext in ipairs(plop_extension_stack) do
    ext.at_specialization(wrapper)
  end
end
function installed_extensions()
  return newlist{ unpack(plop_extension_stack) }
end

Exports.extend                = add_extensions
Exports.extensions = {
  installed_extensions  = installed_extensions,
  new_extension         = new_extension,
  is_extension          = is_extension,
}

-------------------------------------------------------------------------------

local Interpreter   = {}
Interpreter.__index = Interpreter
local function is_interpreter(obj) return getmetatable(obj) == Interpreter end

-- Expression Interpretation
--  Interp : Expr --> X
--      deref : X,Prim --> X
--        add : X,X --> X
--        mul : X,X --> X
--   variable : name,Prim --> X
--     idxvar : name --> X
--      const : num --> X
--        ptr : nil --> X
local interpreter_methods = { 'deref', 'add', 'mul', 'const',
                              'ptr', 'variable', 'idxvar' }
local function set_as_interpreter(obj)
  for _,fname in ipairs(interpreter_methods) do
    if not type(obj[fname]) == 'function' then
      error("interpreter must have '"..fname.."' member function", 2)
  end end
  return setmetatable(obj, Interpreter)
end

-- pre-declared earlier
function public_sym_convert(sym) return tostring(sym) end
function public_prim_convert(prim)
  return prim and primitive_wrappers[prim] end
local function public_sym_to_private(pub, err_level)
  return pub
  --err_level = (err_level or 1)+1
  --if not type(pub) == 'string' then error('expected string',err_level) end
  --if string.find(pub, "^%d+$") then -- number
  --  return pub
  --elseif is_id_str(pub) then -- number
  --  return construct(pub)
  --else error('invalid string pattern for variable symbol', err_level) end
end

function E.Add:Interpret(interpreter)
  local val = interpreter.const( self.const )
  for _,e in ipairs(self.exprs) do
    val = interpreter.add( val, e:Interpret(interpreter) )
  end
  return val
end
function E.Mul:Interpret(interpreter)
  local val = interpreter.const( self.const )
  for _,e in ipairs(self.exprs) do
    val = interpreter.mul( val, e:Interpret(interpreter) )
  end
  return val
end
function E.DeRef:Interpret(interpreter)
  return interpreter.deref( self.expr:Interpret(interpreter),
                            public_prim_convert(self.prim) )
end
function E.Const:Interpret(interpreter)
  return interpreter.const( self.val )
end
function E.Var:Interpret(interpreter)
  return interpreter.variable( public_sym_convert(self.name),
                               public_prim_convert(self.type) )
end
function E.Idx:Interpret(interpreter)
  return interpreter.idxvar( public_sym_convert(self.name),
                             public_prim_convert(self.type) )
end
function E.Ptr:Interpret(interpreter)
  return interpreter.ptr()
end



local function eval_sizeof(layout, interpreter, opts)
  if not is_physical(layout) then
    error('expected a physical layout as the first argument', 2) end
  if not is_interpreter(interpreter) then
    error('expected interpreter as the second argument', 2) end
  if not is_random_access(layout._decl) then
    error('cannot symbolically evaluate the size of a layout '..
          'that is not randomly accessible', 2) end

  local size

  local env = New_Recursive_Environment()
  if type(opts) == 'table' and opts.no_expand then
    size  = const_size(layout._decl, env)
  else
    size  = offsize(layout._decl, env, PtrVar)
  end
  local result = size:Interpret(interpreter)
  -- environment may have errors due to binding in the interpreter
  -- not being exposed to Recursive_Environment; that's ok
  return result
end
local function static_sizeof(layout)
  local e = const_sizeof_decl(layout._decl)
  return e and e.val or nil
end

local function eval_offset(layout, path, interpreter)
  if not is_physical(layout) then
    error('expected a physical layout as the first argument', 2) end
  if not terralib.israwlist(path) then
    error('expected a list as the second argument', 2) end
  if not is_interpreter(interpreter) then
    error('expected interpreter as the third argument', 2) end
  if not is_random_access(layout._decl) then
    error('cannot symbolically evaluate an offset into a layout '..
          'that is not randomly accessible', 2) end

  -- convert path
  local tkns = newlist()
  local subdecl = layout._decl
  for i,v in ipairs(path) do
    if is_ptr_decl(subdecl) then
      if not type(v) == 'table' then
        error('expected a table (representing pointer dereference) '..
              'as path entry #'..i, 2) end
      tkns:insert(P.DeRef)
      subdecl = subdecl.typ
    elseif is_array_decl(subdecl) then
      if not is_var_str(v) then
        error("expected id or anonymous (size_instance) string "..
              "(representing array indexing) as path entry #"..i, 2) end
      local sym = public_sym_to_private(v,2)
      local size = subdecl.sizevar
      if not size == sym then
        error("expected '"..tostring(size).."' (representing array "..
              "indexing) as path entry #"..i, 2) end
      tkns:insert(P.Index(sym))
      subdecl = subdecl.typ
    elseif is_struct_decl(subdecl) then
      local subrec
      if type(v) == 'string' then -- convert strings to which field #
        local name = v
        v = subdecl:find_entry(name)
        if not v then
          error("could not find field name '"..name.."' at path entry #"..i..
                " in the struct", 2) end
      end
      if is_uint(v) then
        if v == 0 or v > #subdecl.entries then
          error("field number "..v.." for struct at path entry #"..i..
                " was not in the range 1-"..tostring(#subdecl.entries), 2) end
        subrec = subdecl.entries[v]
      else
        error("expected field name or field number (representing field "..
              "selection from a struct) as path entry #"..i, 2)
      end
      if not subrec.typ then
        error("struct access at path entry #"..i.." was not a sub-tree", 2) end
      tkns:insert(P.Field(subrec.name))
      subdecl = subrec.typ
    elseif is_prim_decl(subdecl) then
      error('Reached primitive sub-tree of layout, but still have path '..
            'entries.  At #'..i, 2)
    else assert(false, 'IMPOSSIBLE CASE') end
  end


  local env       = New_Recursive_Environment()
  local off_expr  = pathoff(layout._decl, env, PtrVar, unpack(tkns))
  local result    = off_expr:Interpret(interpreter)
  -- environment may have errors due to binding in the interpreter
  -- not being exposed to Recursive_Environment; that's ok
  return result
end


Exports.extensions.is_interpreter       = is_interpreter
Exports.extensions.set_as_interpreter   = set_as_interpreter
Exports.extensions.eval_sizeof          = eval_sizeof
Exports.extensions.eval_offset          = eval_offset
Exports.extensions.static_sizeof        = static_sizeof





-- hidden exports.
-- The plop DSL file should hide these from users
-- and use them to hook up the parser etc. to the language callbacks
Exports.parse           = terra_decl_parser
Exports.typecheck       = typecheck_decl
Exports.wrap_physical   = wrap_physical
Exports.wrap_logical    = wrap_logical








