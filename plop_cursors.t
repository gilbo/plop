--[[
  plop - A Small Langauge for abstracting over byte-by-byte details of
          physical layout
    
    by Gilbert Bernstein
    March 2016
    
  See LICENSE
--]]

local PLOP = require 'plop_core'

local Exports = {}
package.loaded["plop_cursors"] = Exports

local newlist = terralib.newlist

local is_prim   = PLOP.is_prim
local is_ptr    = PLOP.is_ptr
local is_array  = PLOP.is_array
local is_struct = PLOP.is_struct


local set_as_interpreter  = PLOP.extensions.set_as_interpreter
local eval_sizeof         = PLOP.extensions.eval_sizeof
local eval_offset         = PLOP.extensions.eval_offset
local static_sizeof       = PLOP.extensions.static_sizeof

-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Free-Variable Analysis & Other Helper Functions
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

-- tries to simultaneously be a dictionary and a list
-- This let's us manage order while still doing quick lookups
-- It also lets us stuff multiple items into a "row" which is nice
local TupleList   = {}
TupleList.__index = TupleList
local function is_tuplelist(obj)
  return getmetatable(getmetatable(obj)) == TupleList
end

local function new_tuplelist(...)
  local tlist = setmetatable({
    list = newlist(),
    dict = {},
  },TupleList)
  if select('#',...) > 0 then tlist:insert(...) end
  return tlist
end
function TupleList:tuples()
  local list = self.list
  local i = 0
  return function()
    i = i+1
    local t = list[i]
    if t then return unpack(t) else return nil end
  end
end
function TupleList:insert(...)
  local key   = select(1,...)
  if key == nil then error('NO NIL KEYS') end
  local tuple = {...}
  self.list:insert(tuple)
  self.dict[key] = tuple
end
function TupleList:get(key)
  return self.dict[key]
end
function TupleList:__new_index()
  error('cannot add fields',2)
end
function TupleList:is_empty()
  return #self.list == 0
end

----------------------

local layout_freevars_weak_cache = setmetatable({},{__mode = "k"})
local function layout_freevars(layout)
  local freevars = layout_freevars_weak_cache[layout]
  if freevars then return freevars end

  if      is_prim(layout)   then freevars = new_tuplelist()
  elseif  is_ptr(layout)    then freevars = layout_freevars(layout:deref())
  elseif  is_array(layout)  then
    local arrayname = layout:arrayvar()
    freevars = layout:arraysize()
           and new_tuplelist()
            or new_tuplelist(arrayname, layout:arraysizetype())
    for name,typ in layout_freevars(layout:arrayelem()):tuples() do
      if name ~= arrayname then freevars:insert(name, typ) end
    end
  elseif is_struct(layout)  then
    local shadow = {}
    freevars = new_tuplelist()
    for _,rec in ipairs(layout:fields()) do if rec.typ then
      if is_prim(rec.typ) then shadow[rec.name] = true
      else for n,t in layout_freevars(rec.typ):tuples() do
        if not shadow[n] then
          freevars:insert(n,t)
          shadow[n] = true
        end
      end end
    end end
  else assert(false,'IMPOSSIBLE CASE') end

  layout_freevars_weak_cache[layout] = freevars
  return freevars
end

local freesizevar_weak_cache = setmetatable({},{__mode = "k"})
local function add_mul_freevars(x,y)
  local vars = new_tuplelist()
  for n,t in x:tuples() do if not vars:get(n) then vars:insert(n,t) end end
  for n,t in y:tuples() do if not vars:get(n) then vars:insert(n,t) end end
  return vars
end
local freesizevar_intepreter = set_as_interpreter({
  deref     = function(x,prim) return x end,
  add       = add_mul_freevars,
  mul       = add_mul_freevars,
  const     = function(c)   return new_tuplelist() end,
  default   = function()    return new_tuplelist() end,
  ptr       = function()    return new_tuplelist() end,
  variable  = function(n,t) return new_tuplelist(n,t) end,
})
local function layout_freesizevars(layout)
  local vars = freesizevar_weak_cache[layout]
  if not vars then
    vars = eval_sizeof(layout,freesizevar_intepreter)
    freesizevar_weak_cache[layout] = vars
  end
  return vars
end

-------------------------------------------------------------------------------

local function new_terra_interp(ptrexpr,varbind,idxbind)
  return set_as_interpreter({
    deref     = function(x, prim)
      local casttyp = prim and &prim:terra_prim() or &&uint8
      return `@[casttyp](x)
    end,
    add       = function(x,y)   return `x + y end,
    mul       = function(x,y)   return `x * y end,
    const     = function(n)     return n end,
    default   = function()      return 0 end,
    ptr       = function()      return ptrexpr end,
    variable  = function(name)  return varbind[name] end,
    idxvar    = function(name)  return idxbind[name] end,
  })
end

local function terraexpr_sizeof(layout, ptr, varbind)
  local interpreter = new_terra_interp(ptr, varbind, {})
  return eval_sizeof(layout, interpreter)
end

-- tkns is a list of path token info
local function terra_offset(layout, tkns, ptr, varbind, idxbind)
  local interpreter = new_terra_interp(ptr, varbind or {}, idxbind or {})
  return eval_offset(layout, tkns, interpreter)
end




-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Physical Cursors
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

local cursor_counter = 0
local cursor_typ_weak_cache = setmetatable({},{__mode="k"})
local function new_cursor_typ(cname_prefix, layout)
  local cursor_typ = cursor_typ_weak_cache[layout]
  if cursor_typ then return cursor_typ end
  cursor_counter = cursor_counter + 1

  -- simple cursor pointer type unless this is a primitive
  local ptrtyp  = &uint8
  if is_prim(layout) then ptrtyp = &layout:terra_prim() end
  -- cursor name
  cname_prefix = cname_prefix or '_'..cursor_counter
  local cname = cname_prefix..'_cursor'

  -- build up a bunch of variable information here
  local freevars, sizevars  = new_tuplelist(), new_tuplelist()
  local freesyms, sizesyms  = newlist(), newlist()
  for n,t in layout_freevars(layout):tuples() do
    local sym = symbol( t:terra_prim(), n )
    freevars:insert(n, sym, t)
    freesyms:insert(sym)
  end
  for n,t in layout_freesizevars(layout):tuples() do
    local _,sym,_ = freevars:get(n)
    if not sym then sym = symbol( t:terra_prim(), n ) end
    sizevars:insert(n, sym, t)
    sizesyms:insert(sym)
  end

  -- construct the Terra structure for the cursor
  local sizes_struct = terralib.types.newstruct('sizes_struct')
  for name,_,prim in freevars:tuples() do
    sizes_struct.entries:insert{ field=tostring(name),
                                 type=prim:terra_prim() }
  end
  local struct ImplementStruct {
    ptr   : ptrtyp
    sizes : sizes_struct
  }
  local struct cursor_typ {
    __hidden : ImplementStruct
  }
  function cursor_typ.metamethods.__typename() return cname end
  layout._cursor_typ = cursor_typ

  ----------------

  local function install_ptr_func()
    cursor_typ.methods.ptr =
      macro(function(self) return `self.__hidden.ptr end,
            function(self) return self.__hidden.ptr end)
  end

  local function install_sizeof()
    -- prepare values
    local csym      = symbol(cursor_typ, 'cursor')
    local bindings  = {}
    for name,_,_ in freevars:tuples() do
      bindings[name] = `csym.__hidden.sizes.[name]
    end
    local size_code = terraexpr_sizeof(layout, `csym.__hidden.ptr, bindings)
    local const_size = static_sizeof(layout)

    -- install way to compute size
    cursor_typ.methods.sizeof =
      macro(function(self)
        if const_size then return const_size
        elseif self then return quote var [csym] = self in [size_code] end
        else error('this cursor type requires sizeof() to be called on '..
                   'instances of cursors') end
      end,function() return const_size end)
  end

  local function install_new()
    terra cursor_typ.methods.New( ptr : &opaque, [freesyms] )
      var c : cursor_typ
      c.__hidden.ptr = [ptrtyp](ptr)
      escape for name,sym,_ in freevars:tuples() do
        emit quote c.__hidden.sizes.[name] = [ sym ] end
      end end
      return c
    end
  end

  -- Don't call this one directly
  -- install method call version of alloc on cursors to pointers
  local function install_alloc_ptr()
    -- edge case, if we have a pointer to a pointer, it's simpler
    local sublayout = layout:deref()
    if is_ptr(sublayout) then
      terra cursor_typ:alloc( alloc : {uint64}->{&opaque} )
        @[&&uint8](self.__hidden.ptr) = [&uint8]( alloc( [sizeof(&uint8)] ) )
      end
      return
    end

    local csym      = symbol(&cursor_typ, 'cursor')
    -- figure out where sizes are coming from
    local sizes_out, sizes_in = newlist(), newlist()
    local suballoc = sublayout._cursor_typ.methods.alloc
    for name,typ in layout_freesizevars(sublayout):tuples() do
      if freevars:get(name) then
        sizes_out:insert(`csym.__hidden.sizes.[name])
      else
        local sym = symbol(typ:terra_prim(), name)
        sizes_in:insert(sym)
        sizes_out:insert(sym)
      end
    end

    cursor_typ.methods.alloc =
      terra( [csym], alloc : {uint64}->{&opaque}, [sizes_in] )
        @[&&uint8](csym.__hidden.ptr) =
          [&uint8](suballoc(alloc, [sizes_out]).__hidden.ptr)
      end
  end

  local function install_alloc()
    local bindings = {}
    for name,sym,_ in sizevars:tuples() do bindings[name] = sym end
    local terra alloc_helper( alloc : {uint64}->{&opaque}, [sizesyms] )
      -- note that we're assuming every relevant size variable has been bound
      var n_bytes = [terraexpr_sizeof(layout, nil, bindings)]
      return [ptrtyp]( alloc(n_bytes) )
    end

    if is_ptr(layout) then
      install_alloc_ptr()
    else
      cursor_typ.methods.alloc =
        terra( alloc : {uint64}->{&opaque}, [sizesyms] )
          var c : cursor_typ
          c.__hidden.ptr = alloc_helper( alloc, [sizesyms] )
          return c
        end
    end
  end

  local function install_free()
    if is_ptr(layout) then
      -- when there's a pointer in the layout, free the data behind it
      terra cursor_typ:free( free : {&opaque}->{} )
        free(@[&&opaque](self.__hidden.ptr))
      end
    else
      -- otherwise, free the memory being referred to by the cursor directly
      cursor_typ.methods.free = terra( c : cursor_typ, free : {&opaque}->{} )
        free(c.__hidden.ptr)
      end
    end
  end

  ----------------

  local function prim_access_wrap(cursor,sublayout)
    if is_prim(sublayout) then
      return `@(cursor:ptr())
    else return cursor end
  end

  local function get_subptr_typ(sublayout)
    return is_prim(sublayout) and &sublayout:terra_prim() or &uint8
  end

  local function metaprog_step(token, sublayout, subcursor_typ, idxbind)
    -- set-up the types
    local c           = symbol(cursor_typ,'cursor')
    local sub_c       = symbol(subcursor_typ,'sub_cursor')
    local sub_ptrtyp  = get_subptr_typ(sublayout)

    -- assemble the code-generation environment
    local ptrexpr = `c.__hidden.ptr
    local varbind = {}
    for name,_,_ in freevars:tuples() do
      varbind[name] = `c.__hidden.sizes.[name] end

    -- metaprogram code to advance the cursor
    local step_code = quote
      sub_c.__hidden.ptr = [sub_ptrtyp]([ 
        terra_offset(layout, {token}, ptrexpr, varbind, idxbind)
      ])
      escape for name,prim in layout_freevars(sublayout):tuples() do
        local sztyp  = prim:terra_prim()
        local szexpr = varbind[name]
        if not szexpr then
          szexpr = terra_offset(layout, {name}, ptrexpr, varbind)
          szexpr = `@[&sztyp](szexpr)
        end
        emit quote sub_c.__hidden.sizes.[name] = szexpr end
      end end
    end
    return c, sub_c, step_code
  end

  -- insert error checking code
  local layout_type = (is_prim(layout) and tostring(layout))
                   or (is_ptr(layout) and "Ptr")
                   or (is_array(layout) and "Array")
                   or (is_struct(layout) and "Struct")
                   or "UNKNOWN"
  cursor_typ.metamethods.__apply = macro(function(c,arg)
    local op_str = arg and " indexed" or " dereferenced"
    error("Cursor "..cname.." has type "..layout_type..
          " so it cannot be"..op_str)
  end)
  cursor_typ.metamethods.__entrymissing = macro(function(field,c)
    error("Cursor "..cname.." has type "..layout_type..
          " so it does not have a field '"..field.."'' to access.")
  end)

  -- handle cases for different kinds of Layouts
  if is_prim(layout) then
    -- nothing to do
  elseif is_ptr(layout) then
    local sublayout     = layout:deref()
    local subcursor_typ = new_cursor_typ(cname_prefix..'_p', sublayout)

    local c, sub_c, step_code =
      -- {} stands for a dereference token
      metaprog_step( {}, sublayout, subcursor_typ )

    local has_sub_array = is_array(sublayout)
    cursor_typ.metamethods.__apply = macro(function(cursor,arg)
      local code = quote
        var [c] = cursor
        var [sub_c]
        [step_code]
      in sub_c end
      if arg and not has_sub_array then
        error('should not pass argument to deref')
      elseif arg and has_sub_array then
        return `code(arg)
      else
        return prim_access_wrap(code, sublayout)
      end
    end)
    -- if sub-structure is a struct, then expose convenience accessors
    if is_struct(sublayout) then
      cursor_typ.metamethods.__entrymissing = macro(function(field,c)
        return `c().[field]
      end)
    end

  elseif is_array(layout) then
    local arrayvar = layout:arrayvar()
    cname_prefix = cname_prefix..'_'..arrayvar
    local sublayout     = layout:arrayelem()
    local subcursor_typ = new_cursor_typ(cname_prefix, sublayout)

    local sizetype  = uint64
    local idx       = symbol(sizetype, tostring(arrayvar))
    local c, sub_c, step_code =
      metaprog_step( arrayvar, sublayout, subcursor_typ,
                     { [arrayvar] = idx } )

    cursor_typ.metamethods.__apply = macro(function(cursor,i)
      return prim_access_wrap(quote
        var [idx]   = [sizetype](i)
        var [c]     = cursor
        var [sub_c]
        [step_code]
      in [sub_c] end, sublayout)
    end)

  elseif is_struct(layout) then
    local advance_table = {} -- gonna hold metaprogramming results
    for _,rec in ipairs(layout:fields()) do
      if rec.typ then
        local subname_prefix  = cname_prefix..'_'..rec.name
        local subcursor_typ   = new_cursor_typ(subname_prefix, rec.typ)

        if rec.name ~= '_' then
          local c, sub_c, step_code =
            metaprog_step( rec.name, rec.typ, subcursor_typ )
          advance_table[rec.name] = {
            c               = c,
            sub_c           = sub_c,
            step_code       = step_code,
            typ             = rec.typ,
          }
        end
      elseif rec.val then
        advance_table[rec.name] = { const_val = rec.val }
      end
    end

    cursor_typ.metamethods.__entrymissing = macro(function(field,c)
      local lookup = advance_table[field]
      if lookup and lookup.const_val then
        return lookup.const_val
      elseif lookup then
        return prim_access_wrap(quote
          var [lookup.c] = c
          var [lookup.sub_c]
          [lookup.step_code]
        in [lookup.sub_c] end, lookup.typ)
      else
        error("cursor does not have member-cursor "..field)
      end
    end)
  else assert(false,'INTERNAL: impossible case') end

  -- Now that we're done recursing, install all the other
  -- helpful generic functions
  install_ptr_func()
  install_sizeof()
  install_new()
  install_alloc()
  install_free()

  cursor_typ.metamethods._is_a_cursor_type = true
  cursor_typ_weak_cache[layout] = cursor_typ

  return cursor_typ
end
local function is_cursor(obj)
  return terralib.types.istype(obj) and obj:isstruct()
                                    and obj.metamethods._is_a_cursor_type
end


-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Logical Cursors
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------


-------------------------------------------------------------------------------


-- returns a cursor for the given logical declaration
-- backed by a cursor for the given physical declaration
local logical_cursor_weak_cache = setmetatable({},{__mode="k"})
local function logical_cursor_weak_get(llayout,playout)
  local sub_cache = logical_cursor_weak_cache[llayout]
  if not sub_cache then
    logical_cursor_weak_cache[llayout] = setmetatable({},{__mode="k"})
    return nil
  else return sub_cache[playout] end
end
local function logical_cursor_weak_set(llayout,playout, val)
  logical_cursor_weak_cache[llayout][playout] = val
end

local function new_logical_cursor(
  cname_prefix, llayout, playout,
  path_tokens, idxvars
)
  local lcursor_typ   = logical_cursor_weak_get(llayout,playout)
  if lcursor_typ then return lcursor_typ end
  cursor_counter      = cursor_counter + 1
  cname_prefix        = cname_prefix or '_'..cursor_counter
  local cname         = cname_prefix..'_lcursor'

  -- manage index variables
  path_tokens = path_tokens or newlist()
  idxvars = idxvars or {} -- map from symbol-name-strings
                          -- to #occurences in path_tokens

  -- build the Cursor struct
  --  stores a backing physical cursor plus index variables
  local IdxStruct = terralib.types.newstruct('IdxStruct')
  for namestr,count in pairs(idxvars) do
    for k=0,count-1 do
      -- uint64 here may be overkill in a lot of cases?
      IdxStruct.entries:insert{ field='_'..namestr..'_'..k, type=uint64 }
    end
  end
  local pcursor_typ = playout._cursor_typ
  local struct lcursor_typ {
    __p_cursor : pcursor_typ
    __idx_vars : IdxStruct
  }
  function lcursor_typ.metamethods.__typename() return cname end

  local function install_translations()
    if next(idxvars) == nil then
      terra lcursor_typ.methods.New( pc : pcursor_typ )
        var lc : lcursor_typ
        lc.__p_cursor = pc
        return lc
      end
      terra lcursor_typ:physical_cursor() : pcursor_typ
        return self.__p_cursor
      end
    end
  end

  -- helper routine
  local function copy_counts(idxcounts)
    local newcounts = {}
    for namestr,count in pairs(idxcounts) do newcounts[namestr] = count end
    return newcounts
  end

  -- build up a list of quoted expressions representing the
  -- index-variables currently available in the cursor or sub-cursor
  --  (optionally takes a new argument for sub-cursor use case)
  local function idx_exprs(cursor, idxcounts, idxname, idxsym)
    -- put identical names into a queue s.t. name_0 comes out before name_1
    local exprs = {}
    -- new name values are enqueued behind existing matching names
    if idxname then exprs[idxname] = newlist{ idxsym } end
    for namestr,count in pairs(idxcounts) do
      local list = exprs[namestr] or newlist()
      exprs[namestr] = list
      for k=1,count do
        local id = count-k
        list:insert( `cursor.__idx_vars.['_'..namestr..'_'..id] )
      end
    end
    return exprs
  end

  -- more complicated than it should be really...
  local function advance_cursor(cursor,tokens,idx_exprs)
    local sublayout = playout
    for k,tkn in ipairs(tokens) do
      if      is_ptr(sublayout) then
        assert(type(tkn) == 'table')
        cursor        = `cursor()
        sublayout     = sublayout:deref()
      elseif  is_array(sublayout) then
        assert(type(tkn) == 'string')
        local idx_e   = assert(idx_exprs[tkn]:remove())
        cursor        = `cursor(idx_e)
        sublayout     = sublayout:arrayelem()
      elseif  is_struct(sublayout) then
        assert(type(tkn) == 'string')
        cursor        = `cursor.[tkn]
        sublayout     = sublayout:fields()[sublayout:findfield(tkn)].typ
      else error('Impossible case') end
    end
    return cursor
  end

  local function advance_idx(unused_tokens, idx_src_exprs, idx_dst_exprs)
    local code = newlist()
    -- checking idx_src_exprs is a bit of an odd hack.  Oh well
    for _,tkn in ipairs(unused_tokens) do if idx_src_exprs[tkn] then
      local src = assert(idx_src_exprs[tkn]:remove())
      local dst = assert(idx_dst_exprs[tkn]:remove())
      code:insert(quote dst = src end)
    end end
    for n,es in pairs(idx_src_exprs) do assert(#es == 0) end
    for n,es in pairs(idx_dst_exprs) do assert(#es == 0) end
    return code
  end

  -- returns used_token_list, unused_token_list, sub_playout, idxleft
  local function path_to_advance_on(tokens, has_match, idxname)
    local cur_layout  = playout
    local used_path   = newlist()
    local idxleft     = copy_counts(idxvars)
    if idxname then idxleft[idxname] = (idxleft[idxname] or 0) + 1 end
    if not has_match then
      return used_path, tokens, cur_layout, idxleft
    end

    local function decidx(name)
      local val = idxleft[name]
      idxleft[name] = (val == 1) and nil or (val-1)
    end

    -- use tokens to advance the layout downward
    while true do
      local did_advance = false

      if is_prim(cur_layout) or type(cur_layout) == 'number' then
        if #tokens == 0 then break end -- ok if we're done
        error('should not try to advance primitives or constants...')
      elseif is_ptr(cur_layout) then
        used_path:insert( {} )
        cur_layout = cur_layout:deref()
        did_advance = true -- 
      elseif is_array(cur_layout) then
        local sizevar = cur_layout:arrayvar()
        for k,tkn in ipairs(tokens) do
          if sizevar == tkn then
            tokens:remove(k)
            used_path:insert(tkn)
            decidx(tkn)
            cur_layout  = cur_layout:arrayelem()
            did_advance = true; break -- continue loop
        end end
      elseif is_struct(cur_layout) then
        local early_exit = false
        for k,tkn in ipairs(tokens) do
          local i = cur_layout:findfield(tkn)
          if i then 
            local rec = cur_layout:fields()[i]
            tokens:remove(k)
            used_path:insert(tkn)
            cur_layout = rec.typ or rec.val
            did_advance = true; break -- continue loop
        end end
      else error('impossible branch') end

      if not did_advance then break end -- exit if we couldn't advance
    end

    return used_path, tokens, cur_layout, idxleft
  end

  local layout_type = (is_prim(llayout) and tostring(llayout))
                   or (is_ptr(llayout) and "Ptr")
                   or (is_array(llayout) and "Array")
                   or (is_struct(llayout) and "Struct")
                   or "UNKNOWN"
  lcursor_typ.metamethods.__apply = macro(function(c,arg)
    error("Cursor "..cname.." has type "..layout_type..
          " so it cannot be indexed")
  end)
  lcursor_typ.metamethods.__entrymissing = macro(function(field,c)
    error("Cursor "..cname.." has type "..layout_type..
          " so it does not have a field '"..field.."'' to access.")
  end)

  if is_prim(llayout) then
    -- nothing to do.
  elseif is_array(llayout) then
    local newidxname      = llayout:arrayvar()
    local matches_playout = is_array(playout)
                        and playout:arrayvar() == newidxname

    -- compute various path manipulations to advance
    local alltokens   = newlist{ newidxname, unpack(path_tokens) }
    local used,unused, sub_playout, idxleft =
      path_to_advance_on(alltokens, matches_playout, newidxname)
    
    -- compute the recursive call
    cname_prefix = cname_prefix..'_'..newidxname
    local sub_lcursor_typ = new_logical_cursor(
      cname_prefix, llayout:arrayelem(), sub_playout, unused, idxleft
    )

    -- build the code
    local c, sub_c  = symbol(lcursor_typ,'c'), symbol(sub_lcursor_typ,'sub_c')
    local idxtype   = uint64
    local idxsym    = symbol( idxtype, 'idxsym' )
    local src_exprs = idx_exprs(c, idxvars, newidxname, idxsym)
    local dst_exprs = idx_exprs(sub_c, idxleft)
    local step_code = advance_cursor(`c.__p_cursor, used, src_exprs)
    local is_raw_expr = is_prim(llayout:arrayelem())
    if not is_raw_expr then
      step_code = quote
        sub_c.__p_cursor = [ step_code ]
        [ advance_idx(unused, src_exprs, dst_exprs) ]
      end
    end

    lcursor_typ.metamethods.__apply = macro(function(cursor,i)
      if is_raw_expr then
        return quote
          var [idxsym]  = [idxtype](i)
          var [c]       = cursor
        in step_code end
      else
        return quote
          var [idxsym]  = [idxtype](i)
          var [c]       = cursor
          var [sub_c]
          [step_code]
        in [sub_c] end
      end
    end)
  elseif is_struct(llayout) then
    local advance_table = {} -- gonna hold metaprogramming results
    for _,lrec in ipairs(llayout:fields()) do
      if lrec.typ then
        --local Ftoken          = P.Field(lrec.name)
        local Ftoken          = lrec.name
        local matches_playout = is_struct(playout)
                            and playout:findfield(lrec.name) ~= nil

        -- compute various path manipulations to advance
        local alltokens = newlist{ Ftoken, unpack(path_tokens) }
        local used, unused, sub_playout, idxleft =
          path_to_advance_on(alltokens, matches_playout)

        local subname_prefix  = cname_prefix..'_'..lrec.name
        local sub_lcursor_typ = new_logical_cursor(
          cname_prefix, lrec.typ, sub_playout, unused, idxleft
        )

        -- build the code
        if lrec.name ~= '_' then
          local c         = symbol(lcursor_typ,'c')
          local src_exprs = idx_exprs(c, idxvars)
          local adv_c     = advance_cursor(`c.__p_cursor, used, src_exprs)
          if is_prim(lrec.typ) then
            local leaf_code = adv_c
            advance_table[tostring(lrec.name)] = {
              c               = c,
              leaf_code       = adv_c,
            }
          else
            local sub_c     = symbol(sub_lcursor_typ,'sub_c')
            local dst_exprs = idx_exprs(sub_c, idxleft)
            local step_code = quote
              sub_c.__p_cursor = [ adv_c ]
              [ advance_idx(unused, src_exprs, dst_exprs) ]
            end

            advance_table[tostring(lrec.name)] = {
              c               = c,
              sub_c           = sub_c,
              step_code       = step_code,
            }
          end
        end
      elseif lrec.val then
        advance_table[tostring(lrec.name)] = { const_val = lrec.val }
      end
    end

    lcursor_typ.metamethods.__entrymissing = macro(function(field,c)
      local lookup = advance_table[field]
      if not lookup then
        error("cursor does not have member-cursor "..field) end
      if lookup.const_val then
        return lookup.const_val
      elseif lookup.leaf_code then
        return quote var [lookup.c] = c in [lookup.leaf_code] end
      else
        return quote
          var [lookup.c] = c
          var [lookup.sub_c]
          [lookup.step_code]
        in [lookup.sub_c] end
      end
    end)

  else assert(false,'INTERNAL: impossible case') end

  install_translations()
  lcursor_typ.metamethods._is_a_cursor_type = true

  logical_cursor_weak_set(llayout,playout, lcursor_typ)
  return lcursor_typ
end


-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- More Conveniences to stick on cursors
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------

local donothing_method = macro(function() return {} end)

-- see wrapper below
local function install_free_all(layout)
  local cursor = layout:cursor()
  if layout:is_prim() then
    return donothing_method
  elseif layout:is_ptr() then
    local sub_func = install_free_all(layout:deref())
    local free_all = terra( c : cursor, free : {&opaque}->{} )
      sub_func(c(), free)
      c:free(free)
    end
    cursor.methods.free_all = free_all
    return free_all
  elseif layout:is_array() then
    local sub_func = install_free_all(layout:arrayelem())
    if sub_func == donothing_method then
      cursor.methods.free_all = donothing_method
      return donothing_method
    else
      local size      = layout:arraysize()
      local sizename  = layout:arrayvar()
      local free_all = terra( c : cursor, free : {&opaque}->{} )
        var N = [ size or `c.__hidden.sizes.[sizename] ]
        for i=0,N do sub_func(c(i), free) end
      end
      cursor.methods.free_all = free_all
      return free_all
    end
  elseif layout:is_struct() then
    local c, free_func = symbol(cursor), symbol({&opaque}->{})
    local code         = newlist()
    for _,f in ipairs(layout:fields()) do if f.typ then
      local name,typ = f.name,f.typ
      if name then
        local sub_func = install_free_all(typ)
        if sub_func ~= donothing_method then
          code:insert(quote sub_func(c.[name],free_func) end)
        end
      end
    end end
    if #code == 0 then return donothing_method
    else
      local terra free_all( [c], [free_func] ) [code] end
      cursor.methods.free_all = free_all
      return free_all
    end
  else error('unexpected case') end
end





-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Standard Cursors as an Extension Object
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------


-------------------------------------------------------------------------------

local function cursors_init(args)
  for _,prim in ipairs(args.primitives) do
    -- for now, no cursor?
    --function prim:cursor()
    --  error('cannot get cursor to primitive layout', 2)
    --end
  end
  function args.layout_proto:cursor() return self._cursor_typ end
  --args.layout_proto
  --args.physical_proto
  --args.logical_proto
end

local function cursor_at_declaration(layout)
  if PLOP.is_physical(layout) then
    local name          = layout:name()
    local cursor_typ    = new_cursor_typ(name, layout)
    layout._cursor_typ  = cursor_typ
    function cursor_typ:layout() return layout end
    cursor_typ.layout   = cursor_typ.methods.layout

    layout.sizeof = cursor_typ.methods.sizeof
    layout.alloc  = cursor_typ.methods.alloc
    layout.free   = cursor_typ.methods.free
    layout.New    = cursor_typ.methods.New

    if not cursor_typ.methods.free_all then install_free_all(layout) end
  else -- is logical
    -- no cursor should be installed
  end
end

local function cursor_at_specialization(layout)
  local physical_layout = layout:physical_layout()
  local name            = layout:name()
  local cursor_typ      = new_logical_cursor(name, layout, physical_layout)
  layout._cursor_typ    = cursor_typ
  function cursor_typ:layout() return layout end
  cursor_typ.layout     = cursor_typ.methods.layout

  layout.New            = cursor_typ.methods.New

  cursor_typ.methods.free_all = macro(function(c, freefunc)
    return quote c:physical_cursor():free_all(freefunc) end
  end)
end

local CURSORS = PLOP.extensions.new_extension{
  name                = "StandardCursors",
  at_init             = cursors_init,
  at_declaration      = cursor_at_declaration,
  at_specialization   = cursor_at_specialization,
}
CURSORS.is_cursor = is_cursor

Exports.Cursors = CURSORS





