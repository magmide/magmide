(** Example: simple, no-op tactic + print *)
module PV = Proofview

let msg_in_tactic str : unit PV.tactic =
	PV.tclLIFT (PV.NonLogical.make (fun () ->
		Feedback.msg_warning (Pp.str str)))

let printHello : unit PV.tactic =
	let open PV.Notations in
	msg_in_tactic "hello" >>= fun () ->
	Tacticals.tclIDTAC
