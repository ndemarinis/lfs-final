-- Things we need
-- - Multiple tables (via util/ordering)
-- - Packet events (arrival, timeout, skip)
-- - Actions (resubmit, output, learn, drop, increment, alert)
-- - Match criteria


-- Assertions/Properties
--  - Packets arrive at table 0
--  - Packets only get to subsequent tables if resubmitted to them
--  - If there are multiple matches, multiple action sets are executed
open util/ordering[Event] as eo

sig Switch {
	--rules: some Rule
	rules: Match lone -> ActionList
} {
	#rules.ActionList = #rules
}


/*
sig Rule {
	match : one Match,
	action : seq Action,
 	--timeout_actions: seq Action,
} {
	some action
}*/

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

sig Output extends Action {
	-- Port?
	out_packet : one Packet
}

sig Learn extends Action {
	rule: Match -> ActionList, 
	use_packet: one Int
} {
	#rule = 1
	use_packet >= 0
	use_packet <= 1
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
	exec_steps: seq Switch,
	actions_executed: ActionList
} {
	#(exec_steps.inds) = add[#(actions_executed.actions.inds), 1]

	exec_steps.first = pre.switch
	exec_steps.last = post.switch
}

sig Arrival extends Event {
    -- First packet is the one that actually arrives on a switch,
    -- future packets (with modifications) might ensure that the packet changes
	--packet: one Packet
	packet: Packet,
	packets: seq Packet
} {
	actions_executed = get_matching_actions[pre.switch, packet]
	packet = packets[0] -- Initialize the first packet
	#packets = add[#(actions_executed.actions.inds), 1]
}

fact transitions {
	all e: Event - eo/last | {
		let eNext = e.next | {
				e.post = eNext.pre
		}	
	}
}


fact exection_steps {
	all e : Event - Arrival | {
		all idx : e.exec_steps.inds - e.exec_steps.lastIdx | {
			let idx' = add[idx, 1] | {
				-- Make the switch updates
				e.exec_steps[idx'] = execute_if_learn[e.exec_steps[idx], e.actions_executed.actions[idx]]
			}
		}
	}

	all e : Arrival | {
		all idx : e.exec_steps.inds - e.exec_steps.lastIdx | {
			let idx' = add[idx, 1] | {
				-- Make the switch updates
				e.exec_steps[idx'] = execute_if_learn_with_packet[e.exec_steps[idx], e.actions_executed.actions[idx], e.packets[idx]]
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

fact packet_mod_holds {
	-- Packet mod changes the packet, otherwise it remains the same
	all e : Arrival | {
		all idx : e.packets.inds - e.packets.lastIdx | {
			let idx' = add[idx, 1] | {
				e.actions_executed.actions[idx] in PacketMod =>
					e.packets[idx'].match = (e.actions_executed.actions[idx] <: PacketMod).new_match else
					e.packets[idx].match = e.packets[idx'].match
			}
		}
	}

	-- Ensure that output uses the modified packet
	all e : Arrival | {
		all idx : e.packets.inds - e.packets.lastIdx | {
			e.actions_executed.actions[idx] in Output implies
			(e.actions_executed.actions[idx] <: Output).out_packet = e.packets[idx]
		}
	}
	
}

run {
	some e : Arrival | {
    	let a = e.actions_executed  | {
			some l : Learn | {
				l in a.actions.elems -- Learn is in an action list
				l.use_packet = 1 -- Use packet
				l.rule.ActionList != e.packet.match -- Learn differed from learn's match
			}

			-- Force a PacketMod and a learn to be in the same list
			some p : PacketMod | {
				p in a.actions.elems
				p.new_match != e.packet.match
			}
		}
	}
} for 5 but exactly 1 Learn, exactly 5 Switch, 1 Arrival

-- We need to ensure that only learn actions can change switches
assert only_learn_changes {
	all e : Event | {
		all idx : e.exec_steps.inds - e.exec_steps.lastIdx | {
			let idx' = add[idx, 1] | {
				e.exec_steps[idx] != e.exec_steps[idx'] implies
					e.actions_executed.actions[idx] in Learn 
			}
		}
	}
}

check only_learn_changes for 2 but 5 Int, exactly 1 Arrival, 5 Switch, exactly 1 Learn, 3 Match

assert only_packet_mod_changes {
	all e : Arrival | {
		all idx : e.packets.inds - e.packets.lastIdx | {
			let idx' = add[idx, 1] | {
				e.packets[idx].match != e.packets[idx'].match implies
					(e.actions_executed.actions[idx] in PacketMod and
					 e.packets[idx'].match = (e.actions_executed.actions[idx] <: PacketMod).new_match)
			}
		}
	}
}
check only_packet_mod_changes for 2 but 5 Int, exactly 1 Arrival, 5 Switch, exactly 1 PacketMod, 3 Match

/*
	Checks that if there was a rule change, and the match wasn't the initial packet or part of the rule,
	then
	the Learn had use_packet = 1 and the new rule's match was part of the match of a PacketMod
*/
assert packet_mod_precedes_complicated_learn {
	all e : Arrival | {
		all idx : e.packets.inds - e.packets.lastIdx | {
			let idx' = add[idx, 1] | {
				(some e.exec_steps[idx'].rules - e.exec_steps[idx].rules and
				 (e.exec_steps[idx'].rules - e.exec_steps[idx].rules).ActionList !=  
				 	(e.actions_executed.actions[idx] <: Learn).rule.ActionList and
				 (e.exec_steps[idx'].rules - e.exec_steps[idx].rules).ActionList != e.packet.match
				)
				implies
				(e.actions_executed.actions[idx] in Learn and 
				 (e.actions_executed.actions[idx] <: Learn).use_packet = 1 and
				 some (e.actions_executed.actions.subseq[0, idx].elems & PacketMod) and
				 (e.exec_steps[idx'].rules - e.exec_steps[idx].rules).ActionList =
					(e.actions_executed.actions.subseq[0, idx].elems <: PacketMod).new_match
				)
			}
		}
	}
}
check packet_mod_precedes_complicated_learn for 5 but 5 Int, exactly 1 Arrival, 5 Switch, exactly 1 PacketMod, exactly 1 Learn, 3 Match



