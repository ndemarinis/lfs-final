--
-- ovs-single-table-reordering-packet-mod.als
-- Single rule table with reordering of actions executed for a given
-- packet arrival.
--

open util/ordering[Event] as eo

sig Switch {
	rules: Match lone -> ActionList
} {
	-- Each switch should have at most one
	-- of each Match
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

fact one_catchall {
	one CatchallMatch
}

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

sig Packet {
	match: one Match
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
				  --pkts[idx'].match = (acts.actions[idx] <: PacketMod).new_match 
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

-- ****** Examples ******

pred learn_is_executed {
	some e: Event | {
		e.pre.switch != e.post.switch
	}
}

run { learn_is_executed } for 5 but 5 Int, 5 Switch

-- Reordering had some effect on the output if the switch rules were
-- different at the end of the ideal and permuted execution steps.
pred reordering_affects_rules[e: Event] {
	e.exec_steps_ideal.last.rules != e.exec_steps_permuted.last.rules
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


-- ****** Assertions ******

-- Helper functions/preds for assertions

-- Get the last PacketMod executed before an output action in
-- a given ActionList
-- NOTE:  Returns an empty set if the output was not in the ActionList
fun preceeding_packet_mod[a: Action, acts: ActionList] : (set PacketMod) {
	a in acts.actions.elems => {
		let outIdx = acts.actions.idxOf[a] | {
			let preceeding = acts.actions.subseq[0,outIdx] | {
				let maxPmIdx = max[(preceeding :> PacketMod).PacketMod] | {
					preceeding[maxPmIdx]
				}
			}
		}
	} else none
}

-- learns_are_swapped: True if l1 precedes l2 in the executed_actions,
--   but l2 preceeds l1 in the permuted_actions
pred actions_are_swapped[e: Event, a1: Action, a2 : Action] {
	e.executed_actions.actions.idxOf[a1] > e.executed_actions.actions.idxOf[a2] and
 	e.permuted_actions.actions.idxOf[a1] < e.permuted_actions.actions.idxOf[a2] 
}

-- reorder_packet_mod: Constructs a pseudo-bijection. 
-- Part 1: If the last packets differ, then there was a swapping of PacketMods
-- Part 2: If PacketMods were swapped, then the final matches will be different

-- One issue was when the permutation preserved order of PacketMods
-- (Drop, PM1, PM2) & (PM1, PM2, Drop)
-- Takeaway:  Permutations that preserve relative ordering of PacketMods
--            don't affect the final output of the switch, which is good.
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
		all disj pm1, pm2 : (e.executed_actions.actions.elems :> PacketMod) | {
			actions_are_swapped[e, pm1, pm2]
			pm1.new_match != pm2.new_match
		}
		  and 
			-- There are no overlapping PacketMods
			#(e.executed_actions.actions.elems :> PacketMod) = 
				#((e.executed_actions.actions.elems :> PacketMod).new_match)
/*
		all disj pm1, pm2:  (e.executed_actions.actions.elems :> PacketMod) | {
			pm1.new_match != pm2.new_match
		}
*/
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
-- Takeway:  Learn actions that *don't* use packet fields can tolerate reordering with PacketMods.
assert reorder_packet_mod_and_learn_without_using_packet {
	all e : Event | {
		-- All learns that have been moved
		all learn : (e.executed_actions.actions - e.permuted_actions.actions)[Int] <: Learn | {
			(
				-- All learns have unique Matches
				(no Learn.use_packet & 1) and -- No Learns use_packet
				#(e.executed_actions.actions.elems <: Learn) = 
					#((e.executed_actions.actions.elems <: Learn).rule.ActionList) and
				#(e.executed_actions.actions.subseq[0, e.executed_actions.actions.idxOf[learn]][Int] <: PacketMod) !=
					#(e.permuted_actions.actions.subseq[0, e.permuted_actions.actions.idxOf[learn]][Int] <: PacketMod) 
			)
			implies
			(
				e.exec_steps_permuted.last.rules[learn.rule.ActionList] = 
					e.exec_steps_ideal.last.rules[learn.rule.ActionList] 
			)
		}
	}
}
check reorder_packet_mod_and_learn_without_using_packet for 4 but 4 Int, 5 Switch, 7 ActionList, exactly 1 Arrival, 3 Action, 3 PacketMod, 3 Learn


-- permuted_packet_mod_and_learn:
--   If a single learn which uses the current packet has been permuted, and the preceding
--   PacketMod is different, then the switches which result from the execution of that Learn are different
-- Takeaway:  A single learn might add a different rule depending on the current state of the packet when 
-- it's executed--if the ordering of PacketMods changes before a learn, it will learn different rules.
-- RUNTIME: ~90 seconds
assert permuted_packet_mod_and_learn {
	all e : Event | {
		all learn : (e.executed_actions.actions.elems <: Learn) | {
			no (e.executed_actions.actions.elems <: PacketMod).new_match & e.packet.match and
			some PacketMod & e.executed_actions.actions.elems and
			learn.use_packet = 1 and 
			e.executed_actions.actions.idxOf[learn] != e.permuted_actions.actions.idxOf[learn] and 
			preceeding_packet_mod[learn, e.executed_actions].new_match != preceeding_packet_mod[learn, e.permuted_actions].new_match
			implies
			e.exec_steps_ideal[ add[e.executed_actions.actions.idxOf[learn], 1] ].rules != e.exec_steps_permuted[ add[e.permuted_actions.actions.idxOf[learn], 1] ].rules
		}
	}
}
check permuted_packet_mod_and_learn for 5 but 5 Int, exactly 1 Arrival, 7 ActionList

-- Check that only the last PacketMod before an output affects the Output action
-- if reordering occurred before an output
--    and the last PacketMod before an output action is the same,
--  then
--    There should be no effect on the output action
-- Takeaway:  For output actions, only the last PacketMod affects the emitted packet--reordering
-- of other PacketMods can be tolerated (so long as they don't affect other actions, as shown by 
-- the other assertions)
assert only_last_packetmod_affects_output {
	all e: Event | {
		all o1, o2: (e.executed_actions.actions.elems :> Output) | {
				let pm1 = preceeding_packet_mod[o1, e.executed_actions],
						pm2 = preceeding_packet_mod[o2, e.permuted_actions] | {
					-- If two output actions are swapped, but their
					-- immediately preceeding PacketMods are the same...
					(actions_are_swapped[e, o1, o2] and
					(pm1.new_match = pm2.new_match))
					implies
					-- The two output actions should be equal
					(o1.out_packet.match = o2.out_packet.match)

					-- If we canonicalize outputs, we can write the following insetad:
					--(o1.out_packet = o2.out_packet)
				}
		}
	}
}
check only_last_packetmod_affects_output for 5 but 5 int, 5 Switch, 7 ActionList, exactly 1 Arrival


-- If a reordering of learns had some effect on the
-- rule tables, there were some number of reordered learns that had
-- the same match criteria.
-- For all events: 
--  If the reordering affects the rules:
--    For all disjoint Learns l1 & l2:
--  	  If they are swapped between the regular list and permuted list
--        and they have the same match, but different action lists
--      Then
--        The final steps have different ActionLists for that match
-- Takeaway:  Ordering of learns with the same match criteria must be preserved in order to
--            not affect the final switch rules.
-- RUNTIME: Takes about 3 minutes to run
-- e.exec_steps_ideal.last != e.exec_steps_permuted.last
assert reordered_learns_causes_effect {
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
check reordered_learns_causes_effect for 4 but 4 Int, 5 Switch, 7 ActionList, exactly 1 Arrival, 0 Action, exactly 2 Learn


--
-- For all events
-- 	For all match
--    If last learn with a given match is different and they have different action lists
--    then
--      Reordering affects installed rules (without PacketMod)
--
-- Takeaway:  If there are multiple learn actions with the same match criteria and different
--           	Action lists, changing the last of those learns to execute for a given match 
--            will alter the switch rules.
assert reordered_learns_causes_effect2 {
	all e: Event | {
		let learns = (e.executed_actions.actions.elems :> Learn),
				executed_acts = (e.executed_actions.actions),
				permuted_acts = (e.permuted_actions.actions) | {
			all m: learns.rule.ActionList | {
				let lastExecIdx = max[executed_acts.rule.ActionList.m],
					  lastPermIdx = max[permuted_acts.rule.ActionList.m] | {
							-- ActionLists must be different
							executed_acts[lastExecIdx].rule[m] != permuted_acts[lastPermIdx].rule[m]
							implies
							reordering_affects_rules[e]
				}
			}
		}
	}
}
check reordered_learns_causes_effect2 for 4 but 4 Int, 5 Switch, 7 ActionList, exactly 1 Arrival, 0 Action, exactly 4 Learn


-- ***** OpenFlow execution assertions *****

-- Generate an instance in which we have action lists of different sizes
pred some_diff_actionlists[] {
		some a1, a2: ActionList | {
				#a1.actions != #a2.actions
		}
}

diff_actionlists:
run { some_diff_actionlists } for 5 but 5 Int, 5 Switch, 7 ActionList, exactly 1 Arrival

-- last_packet_mod_affects_learn:
--   The last packet modification before a learn affects the installed rule after it's executed
assert last_packet_mod_affects_learn {
	all e : Event | {
		all idx : e.executed_actions.actions.inds - e.executed_actions.actions.lastIdx | {
			let idx' = add[idx, 1] | {
				let last_pm = preceeding_packet_mod[e.executed_actions.actions[idx], e.executed_actions] | {	
					(e.executed_actions.actions[idx] in Learn and
					(e.executed_actions.actions[idx] <: Learn).use_packet = 1)
					implies
					(
					last_pm.new_match->((e.executed_actions.actions[idx] <: Learn).rule[Match]) in e.exec_steps_ideal[idx'].rules
					)
				}
			}
		}
	}
}
check last_packet_mod_affects_learn for 5 but 5 Int, exactly 1 Arrival, 7 ActionList

/*
 *	if there was a rule change, and the match wasn't the initial packet or part of the rule,
 * then 
 *	the Learn had use_packet = 1 and the new rule's match was part of the match of a PacketMod
 */
assert packet_mod_precedes_complicated_learn {
	all e : Arrival | {
		all idx : e.packets.inds - e.packets.lastIdx | {
			let idx' = add[idx, 1] | {
				(some e.exec_steps_ideal[idx'].rules - e.exec_steps_ideal[idx].rules and
				 (e.exec_steps_ideal[idx'].rules - e.exec_steps_ideal[idx].rules).ActionList !=  
				 	(e.executed_actions.actions[idx] <: Learn).rule.ActionList and
				 (e.exec_steps_ideal[idx'].rules - e.exec_steps_ideal[idx].rules).ActionList != e.packet.match
				)
				implies
				(e.executed_actions.actions[idx] in Learn and 
				 (e.executed_actions.actions[idx] <: Learn).use_packet = 1 and
				 some (e.executed_actions.actions.subseq[0, idx].elems & PacketMod) and
				 (e.exec_steps_ideal[idx'].rules - e.exec_steps_ideal[idx].rules).ActionList =
					(e.executed_actions.actions.subseq[0, idx].elems <: PacketMod).new_match
				)
			}
		}
	}
}
check packet_mod_precedes_complicated_learn for 5 but 5 Int, exactly 1 Arrival, 5 Switch, exactly 1 PacketMod, exactly 1 Learn, 3 Match


--Only learn actions can change switche rule states
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

-- Only a PacketMod can cause a rule change
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

