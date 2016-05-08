--
-- ovs-single-table-reordering-packet-mod.als
-- Single rule table with reordering of actions executed for a given
-- packet arrival.
--

open util/ordering[Event] as eo

sig Switch {
	rules: Match lone -> ActionList
} {
	#rules.ActionList = #rules
}

sig ActionList {
	actions: seq Action
} {
		some actions
}

sig Match {
}

lone sig CatchallMatch extends Match {}

abstract sig Action {
} {
  Action in ActionList.actions.elems
}

sig Learn extends Action {
	rule: Match lone -> ActionList
} {
	one rule
}

sig Output extends Action {
	out_packet : one Packet
}

sig Drop extends Action {}
sig Alert extends Action {}

sig PacketMod extends Action {
	new_match: one Match
}

sig State {
	switch: one Switch,
}

abstract sig Event {
	pre, post: State,

	exec_steps_permuted: seq Switch,
	exec_steps_ideal: seq Switch,
	permuted_actions: ActionList,
	executed_actions: ActionList,

} {
	#(exec_steps_permuted.inds) = add[#(permuted_actions.actions), 1]

	#exec_steps_ideal = #exec_steps_permuted

	exec_steps_permuted.first = pre.switch
	exec_steps_ideal.first = pre.switch

	exec_steps_ideal.last = post.switch


	-- **** Reordering ****
	-- The matched actions must be a permutation of the actions that are executed
	is_permutation[permuted_actions.actions,
								 executed_actions.actions]

	-- For now, we can enforce that the actions MUST be reordered
	permuted_actions.actions != executed_actions.actions
}

fact transitions {
	all e: Event - eo/last | {
		let eNext = e.next | {
				e.post = eNext.pre
		}
	}
}


 -- Execution steps with possible reordering
fact execution_steps_permuted {
	all e : Event | {
		all idx : e.exec_steps_permuted.inds - e.exec_steps_permuted.lastIdx | {
			let idx' = add[idx, 1] | {
				-- Make the switch updates
				e.exec_steps_permuted[idx'] = execute_if_learn[e.exec_steps_permuted[idx],
	   																							     e.permuted_actions.actions[idx]]
			}
		}
	}
}

fact execution_steps_ideal {
	all e : Event | {
		all idx : e.exec_steps_ideal.inds - e.exec_steps_ideal.lastIdx | {
			let idx' = add[idx, 1] | {
				-- Make the switch updates
				e.exec_steps_ideal[idx'] = execute_if_learn[e.exec_steps_ideal[idx],
																										e.executed_actions.actions[idx]]
			}
		}
	}
}

fun get_matching_actions[s: Switch, p: Packet] : (ActionList) {
		(p.match in s.rules.ActionList) =>
				s.rules[p.match]
		else { -- Table miss
				s.rules[CatchallMatch]
		}
}


fun execute_if_learn[s: Switch, a: Action]: (Switch) {
		{ s2: Switch | {
			a in Learn =>
				s2.rules = execute_learn[s, (a :> Learn)] else
				s2.rules = s.rules
		}}
}


fun execute_learn[s: Switch, l: Learn] : (Match -> ActionList) {
		s.rules ++ l.rule
}



fact one_catchall {
	one CatchallMatch
}


sig Arrival extends Event {
  -- First packet is the one that actually arrives on a switch,
  -- future packets (with modifications) might ensure that the packet changes
	packet: Packet,         -- Packet that actually arrives on the switch
  packets: seq Packet,     -- Packets as modified during execution of non-reordered actions
	permuted_packets: seq Packet -- Packets as modified using reordered actions
} {
	executed_actions = get_matching_actions[pre.switch, packet]

	-- First packet in the sequences is the one arriving on the switch
	packet = packets[0]
	packet = permuted_packets[0]

	#packets = add[#(executed_actions.actions.inds), 1]
	#packets = #permuted_packets
}


sig Packet {
	match: one Match
}


fact packet_mod_inorder {
  -- If executing a PacketMod at a given step, the new match
  -- criteria in the PacketMod action becomes the packet's match
  -- criteria in the next execution step
	all e : Arrival | {
		all idx : e.packets.inds - e.packets.lastIdx | {
			let idx' = add[idx, 1] | {
				e.executed_actions.actions[idx] in PacketMod =>
					e.packets[idx'].match = (e.executed_actions.actions[idx] <: PacketMod).new_match 
				else {
					--e.packets[idx].match = e.packets[idx'].match
					e.packets[idx] = e.packets[idx']
				}
			}
		}
	}

  -- An output action at a given step uses the match criteria
  -- uses the packet for that execution step.
	all e : Arrival | {
		all idx : e.packets.inds - e.packets.lastIdx | {
			e.executed_actions.actions[idx] in Output =>
			(e.executed_actions.actions[idx] <: Output).out_packet = e.packets[idx]
		}
	}

}


fact packet_mod_reordered {
  -- If executing a PacketMod at a given step, the new match
  -- criteria in the PacketMod action becomes the packet's match
  -- criteria in the next execution step
	all e : Arrival | {
		all idx : e.permuted_packets.inds - e.permuted_packets.lastIdx | {
			let idx' = add[idx, 1] | {
				e.permuted_actions.actions[idx] in PacketMod =>
					e.permuted_packets[idx'].match = (e.permuted_actions.actions[idx] <: PacketMod).new_match 
				else {
					--e.permuted_packets[idx].match = e.permuted_packets[idx'].match
					e.permuted_packets[idx] = e.permuted_packets[idx']
				}
			}
		}
	}

  -- An output action at a given step uses the match criteria
  -- uses the packet for that execution step.
	all e : Arrival | {
		all idx : e.permuted_packets.inds - e.permuted_packets.lastIdx | {
			e.permuted_actions.actions[idx] in Output =>
			(e.permuted_actions.actions[idx] <: Output).out_packet = e.permuted_packets[idx]
		}
	}
}



-- True if one sequence of actions is a permutation of another
-- NOTE:  a sequence with no modifications may be considered a
-- permutation of itself.  This is by design (and can be restricted
-- elsewhere in the model if needed.)
pred is_permutation[s: seq Action, s': seq Action] {
	#s = #s'                   -- Size must be the same
	and s.inds = s'.inds       -- Must have the same indices
	and s.elems = s'.elems     -- Elements must be the same
	-- Finally, the count of each element must be the same
	and (all a: s.elems |
				#(s.indsOf[a]) = #(s'.indsOf[a]))
}




-- Given a packet, find a match on the given tables
fact force_learn {
	some e: Event | {
		e.pre.switch != e.post.switch
	}
}


run { } for 5 but 5 Int, 5 Switch

-- Generate an instance in which we have action lists of different sizes
pred some_diff_actionlists[] {
		some a1, a2: ActionList | {
				#a1.actions != #a2.actions
		}
}

diff_actionlists:
run { some_diff_actionlists } for 5 but 5 Int, 5 Switch, 7 ActionList, exactly 1 Arrival

-- Reordering had some effect on the output if the switch rules were
-- different at the end of the ideal and permuted execution steps.
pred reordering_affects_rules[e: Event] {
	e.exec_steps_ideal.last != e.exec_steps_permuted.last
}

-- Reordering had some effect the packet if the last packet was different
-- TODO:  Check output actions as well.
pred reordering_affects_packets[a: Arrival] {
	a.packets.last.match != a.permuted_packets.last.match
}


has_effect_on_switch:
run { some e: Event |
				reordering_affects_rules[e]
} for 5 but 5 Int, 5 Switch, 7 ActionList, exactly 1 Arrival


pred some_diff_packets[] {
	some a: Arrival |
		reordering_affects_packets[a]			
}

diff_packets:
run { some_diff_packets } for 5 but 5 int, 5 Switch, 7 ActionList, exactly 1 Arrival

--
-- Assertions
-- - Only learn causes executions
-- - Reordered learns with intersecting match criteria implies
--   that reordering had an effect on the flow tables
--

-- We can show that, if a reordering of learns had some effect on the
-- rule tables, there were some number of reordered learns that had
-- the same match criteria.
assert reordered_learns_causes_effect {
	all e: Event /*, disj l1, l2: e.executed_actions.actions.elems*/ | {
			reordering_affects_rules[e] implies
			let amdi = min[((e.executed_actions.actions -
											 e.permuted_actions.actions)).Action] | {
				let d = e.executed_actions.actions.subseq[amdi,
																									e.executed_actions.actions.lastIdx] | {
					--l1 in diff[Int] and l2 in diff[Int] and
					--l1.rule.ActionList = l2.rule.ActionList
					-- If a set of learns has overlapping match criteria, the length
					-- of the set of the match criteria will be smaller than the
					-- set of learns
					#d != #(d.elems.rule.ActionList)
				}
			}
	}
}
check reordered_learns_causes_effect for 5 but 5 Int, 5 Switch, 7 ActionList, exactly 1 Arrival


-- We need to ensure that only learn actions can change switches
assert only_learn_changes {
	all e : Event | {
		all idx : e.exec_steps_permuted.inds - e.exec_steps_permuted.lastIdx | {
			let idx' = add[idx, 1] | {
				e.exec_steps_permuted[idx] != e.exec_steps_permuted[idx'] =>
					e.executed_actions.actions[idx] in Learn else
					e.executed_actions.actions[idx] not in Learn
			}
		}
	}
}

check only_learn_changes for 2 but 5 Int, exactly 1 Arrival, 5 Switch


assert only_packetmod_changes_packet {
	all a: Arrival | {
		all idx: a.packets.inds - a.packets.lastIdx | {
			let idx' = add[idx, 1] | {
					(a.packets[idx] != a.packets[idx']) implies 
						(a.executed_actions.actions[idx] in PacketMod)

					(a.permuted_packets[idx] != a.permuted_packets[idx']) implies 
						(a.permuted_actions.actions[idx] in PacketMod)					
			}
		}
	}
}
check only_packetmod_changes_packet for 5 but 5 Int, exactly 1 Arrival, 7 ActionList