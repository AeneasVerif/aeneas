module T = Types
open TypesUtils
open Values

let mk_unit_value : typed_value = { value = Tuple []; ty = mk_unit_ty }

let mk_typed_value (ty : T.ety) (value : value) : typed_value = { value; ty }
