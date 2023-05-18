structure saveThmsLib =
struct

type simpset = simpLib.simpset;

open HolKernel boolLib markerLib;

val op++ = simpLib.++;
val op-* = simpLib.-*;

val ERR = mk_HOL_ERR "saveThmsLib";

fun add_simpls tyinfo ss =
    (ss ++ simpLib.tyi_to_ssdata tyinfo) handle HOL_ERR _ => ss

(* TODO: what is this? *)
fun tyinfol() = TypeBasePure.listItems (TypeBase.theTypeBase())

datatype stc_update = ADD_SSFRAG of simpLib.ssfrag | REMOVE_RWT of string
type stc_state = simpset * bool * stc_update list
  (* theorems, initialised-flag, update list (most recent first) *)

val initial_simpset = simpLib.empty_ss
fun ssf1 nth = simpLib.empty_ssfrag |> simpLib.add_named_rwt nth

val state0 : stc_state = (initial_simpset, false, [])
fun apply_delta d ((sset,initp,upds):stc_state) : stc_state =
    case d of
        ThmSetData.ADD nth =>
        (sset ++ ssf1 nth, true, [])
      | ThmSetData.REMOVE s => (sset -* [s], true, [])

fun apply_stc_update (ADD_SSFRAG ssf, ss) = ss ++ ssf
  | apply_stc_update (REMOVE_RWT n, ss) = ss -* [n]

(* A stateful theorems collection *)
datatype stc = STC_CON of {
    name        : string,
    thy_ssfrag  : string -> simpLib.ssfrag,
    thy_simpset : string -> simpset option,
    get_ss      : unit -> simpset,
    export_thms : string list -> unit
}

(* Create a stateful theorems collection *)
fun create_stateful_theorem_set (stc_name : string) =
  let
(* val stc_name = "testStc" *)

    fun init_state (st as (sset,initp,upds)) =
        if initp then st
        else
          let fun init() =
                  (List.foldl apply_stc_update sset (List.rev upds)
                              |> rev_itlist add_simpls (tyinfol()),
                   true, [])
          in
            HOL_PROGRESS_MESG ("Initialising STC simpset: " ^ stc_name ^ " ... ", "done") init ()
          end

    fun opt_partition f g ls =
        let
          fun recurse As Bs ls =
              case ls of
                  [] => (List.rev As, List.rev Bs)
                | h::t => (case f h of
                               SOME a => recurse (a::As) Bs t
                             | NONE => (case g h of
                                            SOME b => recurse As (b::Bs) t
                                         | NONE => recurse As Bs t))
        in
          recurse [] [] ls
        end

    (* stale-ness is important for derived values. Derived values will get
       re-calculated if their flag is true when the value is requested.
    *)
    val stale_flags = Sref.new ([] : bool Sref.t list)
    fun notify () =
        List.app (fn br => Sref.update br (K true)) (Sref.value stale_flags)

    fun apply_to_global d (st as (sset,initp,upds):stc_state) : stc_state =
        if not initp then
          case d of
              ThmSetData.ADD nth =>
              let
                open simpLib
                val upds' =
                    case upds of
                        ADD_SSFRAG ssf :: rest =>
                        ADD_SSFRAG (add_named_rwt nth ssf) :: rest
                      | _ => ADD_SSFRAG (ssf1 nth) :: upds
              in
                (sset, initp, upds')
              end
            | ThmSetData.REMOVE s => (sset, initp, REMOVE_RWT s :: upds)
        else
          apply_delta d st before notify()

    fun finaliser {thyname} deltas (sset,initp,upds) =
      let
        fun toNamedAdd (ThmSetData.ADD p) = SOME p | toNamedAdd _ = NONE
        fun toRM (ThmSetData.REMOVE s) = SOME s | toRM _ = NONE
        val (adds,rms) = opt_partition toNamedAdd toRM deltas
        val ssfrag = simpLib.named_rewrites_with_names thyname (List.rev adds)
          (* List.rev here preserves old behaviour wrt to the way theorems were
             added to the global simpset; it will only make a difference when
             overall rewrite system is not confluent *)
        val new_upds = ADD_SSFRAG ssfrag :: map REMOVE_RWT rms
      in
        if initp then
          (List.foldl apply_stc_update sset new_upds, true, []) before notify()
        else (sset, false, List.revAppend(new_upds, upds))
      end


    val adresult as {DB,get_global_value,record_delta,update_global_value,...} =
      ThmSetData.export_with_ancestry {
        delta_ops = {
          apply_delta = apply_delta,
          apply_to_global = apply_to_global,
          thy_finaliser = SOME finaliser,
          initial_value = state0, uptodate_delta = K true
        },
        settype = stc_name
      }

    val get_deltas = #get_deltas adresult

    (*
    (* TODO: what is this? *)
    fun update_fn tyi =
      augment_stc_ss ([simpLib.tyi_to_ssdata tyi] handle HOL_ERR _ => [])

    val () = TypeBase.register_update_fn (fn tyi => (update_fn tyi; tyi))
    *)

    fun get_ss () =
        (update_global_value init_state;
         #1 (get_global_value()))

    fun export_thms slist =
      let val ds = map ThmSetData.mk_add slist
      in
        List.app record_delta ds;
        update_global_value (rev_itlist apply_to_global ds)
      end

    (* assume that there aren't any removes for things added in this theory;
       it's not rational to do that; one should add it locally only, or not
       add it at all
    *)
    fun mkfrag_from thy setdeltas =
      let fun recurse ADDs [] = ADDs
            | recurse ADDs (ThmSetData.ADD p :: rest) = recurse (p::ADDs) rest
            | recurse ADDs (_ :: rest) = recurse ADDs rest
          val ADDs = recurse [] setdeltas
            (* order of addition is flipped; see above for why this is
               "reasonable" *)
      in
        simpLib.named_rewrites_with_names thy ADDs
      end
    fun thy_ssfrag s = get_deltas {thyname=s} |> mkfrag_from s

    fun thy_simpset s = Option.map (#1 o init_state) (DB {thyname=s})
  in
    STC_CON { name = stc_name, thy_ssfrag = thy_ssfrag, thy_simpset = thy_simpset,
              get_ss = get_ss, export_thms = export_thms }
  end

fun rewrite_thms_of_simpset (ss : simpset) : thm list =
  List.concat (map simpLib.frag_rewrites (simpLib.ssfrags_of ss))

(*
(* Create a stateful theorems collection *)
val STC_CON { name = stc_name, thy_ssfrag = thy_ssfrag, thy_simpset = thy_simpset, get_ss = get_ss, export_thms = export_thms } =
  create_stateful_theorem_set "testStc1"

Theorem th1:
  T /\ (T /\ T)
Proof
  fs []
QED

export_thms ["th1"]

fun rewrite_thms_of_simpset (ss : simpset) : thm list =
  List.concat (map simpLib.frag_rewrites (simpLib.ssfrags_of ss))

rewrite_thms_of_simpset (get_ss ())
*)

val STC_CON { name = stc_name, thy_ssfrag = thy_ssfrag, thy_simpset = thy_simpset, get_ss = get_ss, export_thms = export_thms } =
  create_stateful_theorem_set "testStc1"

end
