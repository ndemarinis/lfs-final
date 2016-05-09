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
	rule: Match lone -> ActionList,
	use_packet: one Int
} {
	one rule
	use_packet >= 0
	use_packet <= 1
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
	is_permutation_weak_output[permuted_actions.actions,
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

	all e : Arrival | {
		all idx : e.exec_steps_permuted.inds - e.exec_steps_permuted.lastIdx | {
			let idx' = add[idx, 1] | {
				-- Make the switch updates
				e.exec_steps_permuted[idx'] = execute_if_learn_with_packet[e.exec_steps_permuted[idx],
					e.permuted_actions.actions[idx], e.permuted_packets[idx]]
			}
		}
	}
}

fact execution_steps_ideal {
	all e : Event - Arrival| {
		all idx : e.exec_steps_ideal.inds - e.exec_steps_ideal.lastIdx | {
			let idx' = add[idx, 1] | {
				-- Make the switch updates
				e.exec_steps_ideal[idx'] = execute_if_learn[e.exec_steps_ideal[idx],
																										e.executed_actions.actions[idx]]
			}
		}
	}

	all e : Arrival | {
		all idx : e.exec_steps_ideal.inds - e.exec_steps_ideal.lastIdx | {
			let idx' = add[idx, 1] | {
				-- Make the switch updates
				e.exec_steps_ideal[idx'] = execute_if_learn_with_packet[e.exec_steps_ideal[idx], 
					e.executed_actions.actions[idx], e.packets[idx]]
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

fun execute_if_learn_with_packet[s: Switch, a: Action, p: Packet]: (Switch) {
		{ s2: Switch | { 
			a in Learn =>
				{(a :> Learn).use_packet = 1 =>
					s2.rules = execute_learn_packet[s, (a :> Learn), p] else
					s2.rules = execute_learn[s, (a :> Learn)]
				} else {
				s2.rules = s.rules
				}
		}}
}

fun execute_learn[s: Switch, l: Learn] : (Match -> ActionList) {
		s.rules ++ l.rule
}

fun execute_learn_packet[s: Switch, l: Learn, p: Packet] : (Match -> ActionList) {
	s.rules ++ p.match->l.rule[Match]
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
	-- Define packet modifications and outputs for actions
	-- executed in order
	all e : Arrival | {
		modifyPackets[e.packets, e.executed_actions]
		doOutput[e.packets, e.executed_actions]
	}
}

fact packet_mod_reordered {
	-- Define packet modifications and outputs for
	-- permuted actions
	all e : Arrival | {
		modifyPackets[e.permuted_packets, e.permuted_actions]
		doOutput[e.permuted_packets, e.permuted_actions]
	}
}

pred modifyPackets[pkts: seq Packet, acts: ActionList] {
  -- If executing a PacketMod at a given step, the new match
  -- criteria in the PacketMod action becomes the packet's match
  -- criteria in the next execution step
	all idx : pkts.inds - pkts.lastIdx | {
		let idx' = add[idx, 1] | {
				-- The next packet's match criteria should change if:
				-- 1) The action we're executing is a PacketMod
				-- 2) The packet's match criteria is different from the one in the PacketMod
				-- This ensures Packet atoms only change when we actually modify a field.
				(acts.actions[idx] in PacketMod) && 
				((acts.actions[idx] & PacketMod).new_match != pkts[idx].match) => {
					pkts[idx'].match = (acts.actions[idx] <: PacketMod).new_match 
--				acts.actions[idx] in PacketMod =>
				pkts[idx'].match = (acts.actions[idx] <: PacketMod).new_match 
			} else {
				--e.permuted_packets[idx].match = e.permuted_packets[idx'].match
				pkts[idx] = pkts[idx']
			}
		}
	}

}

pred doOutput[pkts: seq Packet, acts: ActionList] {
  -- An output action at a given step uses the match criteria
  -- uses the packet for that execution step.
	all idx : pkts.inds - pkts.lastIdx | {
		acts.actions[idx] in Output =>
			(acts.actions[idx] <: Output).out_packet = pkts[idx]
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

-- True if one sequence of actions is a permutation of another,
-- all elements in both sequences must be the same EXCEPT for outputs,
-- which may be different atoms if they get reordered.
pred is_permutation_weak_output[s: seq Action, s': seq Action] {
	#s = #s'                   -- Size must be the same
	and s.inds = s'.inds       -- Must have the same indices

	-- Elements must be the same, except outputs
	and (s.elems - Output) = (s'.elems - Output)
	-- The count of each element must be the same
	and (all a: (s.elems - Output) |
				#(s.indsOf[a]) = #(s'.indsOf[a]))

	-- Finally, since we can't use the above assertion on
	-- outputs, just assert that the number of outputs must
	-- be the same.  This allows the individual Output atoms
	-- to change, while keeping the same number of them
	-- Technically, this means that alloy can nondeterministicly pick
	-- which outputs to use, but we enforce which outs belong here
	-- with doOutput
	#(s.elems :> Output) = #(s'.elems :> Output)
}

-- Given a packet, find a match on the given tables

pred learn_is_executed {
	some e: Event | {
		e.pre.switch != e.post.switch
	}
}


run { learn_is_executed } for 5 but 5 Int, 5 Switch

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
pred reordering_affects_packet_processing[a: Arrival] {
	a.packets.last.match != a.permuted_packets.last.match
}

-- Reordering affected packets generated by output actions if
-- the packets included in the output actions are different
pred reordering_affects_output[a: Arrival] {
	let out = a.executed_actions.actions.elems :> Output,
			out' = a.permuted_actions.actions.elems :> Output | {
			out.out_packet != out'.out_packet
	}
}

reordering_affects_rules:
run { learn_is_executed &&
			some e: Event |
				reordering_affects_rules[e]
} for 5 but 5 Int, 5 Switch, 7 ActionList, exactly 1 Arrival


-- Show an example where some packets have changed
pred some_diff_packets[] {
	some a: Arrival | {
		reordering_affects_packet_processing[a]
	}
}

diff_packets:
run { some_diff_packets } for 5 but 5 int, 5 Switch, 7 ActionList, exactly 1 Arrival

pred output_is_executed[a: Arrival] {
	some (a.executed_actions.actions.elems :> Output)
}

pred packet_is_modified[a: Arrival] {
	some pm: (a.executed_actions.actions.elems :> PacketMod) | {
		pm.new_match != a.packet.match
	}
}

-- Show an example where reordering causes different outputs
pred showOutputReordering[] {
	some a: Arrival | {
		some (a.executed_actions.actions.elems :> PacketMod)
		some (a.executed_actions.actions.elems :> Output)
		#(a.executed_actions.actions) = 2 -- Show a minimal example
		output_is_executed[a]
		packet_is_modified[a]
		
		reordering_affects_output[a]
	}
}

run showOutputReordering for 5 but 5 int, 5 Switch, 7 ActionList, 
			exactly 1 Arrival, 0 Learn, 0 Alert, 0 Drop

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


-- learns_are_swapped: True if l1 precedes l2 in the executed_actions,
--   but l2 preceeds l1 in the permuted_actions
pred actions_are_swapped[e: Event, a1: Action, a2 : Action] {
	e.executed_actions.actions.idxOf[a1] > e.executed_actions.actions.idxOf[a2] and
 	e.permuted_actions.actions.idxOf[a1] < e.permuted_actions.actions.idxOf[a2] 
}

-- For all events: 
--  If the reordering affects the rules:
--    For all disjoint Learns l1 & l2:
--  	  If they are swapped between the regular list and permuted list
--        and they have the same match, but different action lists
--      Then
--        The final steps have different ActionLists for that match

-- RUNTIME: Takes about 3 minutes to run
assert reordered_learns_causes_effect2 {
	all e: Event  | {
		reordering_affects_rules[e] implies (
			all disj l1, l2 : Learn | {
				(
 				  -- First two values are if there learns are swapped
				  actions_are_swapped[e, l1, l2] and
				  l1.rule.ActionList = l2.rule.ActionList and -- Same Match
				  l1.rule[Match] != l2.rule[Match]  -- Different Lists
				)
				implies
				(
					e.exec_steps_ideal.last.rules[l1.rule.ActionList] !=
						e.exec_steps_permuted.last.rules[l1.rule.ActionList] 
				)
			}		
		)
	} 
}
check reordered_learns_causes_effect2 for 4 but 4 Int, 5 Switch, 7 ActionList, exactly 1 Arrival, 0 Action, exactly 2 Learn

-- reorder_packet_mod: Constructs a pseudo-bijection. 
-- Part 1: If the last packets differ, then there was a swapping of PacketMods
-- Part 2: If PacketMods were swapped, then the final matches will be different

-- One issue was when the permutation preserved order of PacketMods
-- (Drop, PM1, PM2) & (PM1, PM2, Drop)
assert reorder_packet_mod {
	all e: Arrival  | { 
		-- If the last matches differ, then there was a PacketMod that was swapped
		e.packets.last.match != e.permuted_packets.last.match 
		implies
		(
			some PacketMod & (e.executed_actions.actions - e.permuted_actions.actions)[Int]
		)

		-- If there are 2 packet mods, and they're swapped, then the final 
		-- packet values will be different
		(
		#(PacketMod & e.executed_actions.actions.elems) > 1 and
		all disj pm1, pm2 : PacketMod | {
			actions_are_swapped[e, pm1, pm2]
						pm1 in e.executed_actions.actions.elems
			pm2 in e.executed_actions.actions.elems
			pm1.new_match != pm2.new_match
		}
		  and 
		all disj pm1, pm2: PacketMod | {
			pm1 in e.executed_actions.actions.elems
			pm2 in e.executed_actions.actions.elems
			pm1.new_match != pm2.new_match
		}
		  

		)
		implies
		(
			e.packets.last.match != e.permuted_packets.last.match 
		)
	}
}
check reorder_packet_mod for 4 but 4 Int, 5 Switch, 7 ActionList, exactly 1 Arrival, 3 Action, 3 PacketMod, 2 Learn

-- reorder_packet_mod_and_learn_without_using_packet:
-- If no learns are using the current packet, and the number of PacketMods 
--   change before a given Learn and learns don't overwrite each other,
--  then 
--    the final switches won't see an effect
assert reorder_packet_mod_and_learn_without_using_packet {
	all e : Event | {
		-- All learns that have been moved
		all learn : (e.executed_actions.actions - e.permuted_actions.actions)[Int] <: Learn | {
			(
				-- All learns have unique Matches
				no Learn.use_packet & 1 and -- No Learns use_packet
				#(e.executed_actions.actions.elems <: Learn) = 
					#((e.executed_actions.actions.elems <: Learn).rule.ActionList) and
				#(e.executed_actions.actions.subseq[0, e.executed_actions.actions.idxOf[learn]][Int] <: PacketMod) !=
					#(e.permuted_actions.actions.subseq[0, e.permuted_actions.actions.idxOf[learn]][Int] <: PacketMod) 
			)
			implies
			(
				--	exec_steps_permuted: seq Switch,
                --	exec_steps_ideal: seq Switch,
				e.exec_steps_permuted.last.rules[learn.rule.ActionList] = 
					e.exec_steps_ideal.last.rules[learn.rule.ActionList] 
			)
		}
	}
}
check reorder_packet_mod_and_learn_without_using_packet for 4 but 4 Int, 5 Switch, 7 ActionList, exactly 1 Arrival, 3 Action, 3 PacketMod, 3 Learn

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