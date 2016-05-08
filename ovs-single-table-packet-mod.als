--
-- ovs-single-table-packet-mod.als
-- Single rule table with action to modify packets
-- during rule execution; output action also holds the packet
-- at time output was executed.
--

open util/ordering[Event] as eo

sig Switch {
	--rules: some Rule
	rules: Match lone -> ActionList
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

sig Output extends Action {
	-- Port?
	out_packet : one Packet
}

sig Learn extends Action {
	rule: Match -> ActionList
} {
	#rule = 1
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
	exec_steps: seq Switch,
	actions_executed: ActionList
} {
	#(exec_steps.inds) = add[#(actions_executed.actions.inds), 1]

	exec_steps.first = pre.switch
	exec_steps.last = post.switch
}

fact transitions {
	all e: Event - eo/last | {
		let eNext = e.next | {
				e.post = eNext.pre
		}
	}
}


fact exection_steps {
	all e : Event | {
		all idx : e.exec_steps.inds - e.exec_steps.lastIdx | {
			let idx' = add[idx, 1] | {
				-- Make the switch updates
				e.exec_steps[idx'] = execute_if_learn[e.exec_steps[idx], e.actions_executed.actions[idx]]
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
	--packet: one Packet
	packet: Packet,
	packets: seq Packet
} {
	actions_executed = get_matching_actions[pre.switch, packet]
	packet = packets[0] -- Initialize the first packet
	#packets = add[#(actions_executed.actions.inds), 1]
}

fact packet_mod_holds {
        -- If executing a PacketMod at a given step, the new match
        -- criteria in the PacketMod action becomes the packet's match
        -- criteria in the next execution step
	all e : Arrival | {
		all idx : e.packets.inds - e.packets.lastIdx | {
			let idx' = add[idx, 1] | {
				-- The next packet's match criteria should change if:
				-- 1) The action we're executing is a PacketMod
				-- 2) The packet's match criteria is different from the one in the PacketMod
				-- This ensures Packet atoms only change when we actually modify a field.
				(e.actions_executed.actions[idx] in PacketMod) && 
				((e.actions_executed.actions[idx] & PacketMod).new_match != e.packets[idx].match) => {
						e.packets[idx'].match = (e.actions_executed.actions[idx] <: PacketMod).new_match 
					} else { -- If we weren't executing a PacketMod, the packet itself should not change
						e.packets[idx] = e.packets[idx']
--					e.packets[idx].match = e.packets[idx'].match
					}
			}
		}
	}

       -- An output action at a given step uses the match criteria
       -- uses the packet for that execution step.
	all e : Arrival | {
		all idx : e.packets.inds - e.packets.lastIdx | {
			e.actions_executed.actions[idx] in Output =>
			(e.actions_executed.actions[idx] <: Output).out_packet = e.packets[idx]
		}
	}

}


sig Packet {
	match: one Match
}

-- Facts
--  - Only new rules are added by learns
--  -


fact force_learn {
	some e: Event | {
		e.pre.switch != e.post.switch
	}
}


--run {} for 2 but 5 Int, exactly 1 Arrival, 5 Switch, exactly 1 Learn
/*
run {
	some a : Arrival | {
		#a.packets.elems > 1
	}
} for 2 but 5 Int, exactly 1 Arrival, 5 Switch, 1 PacketMod, exactly 5 Match, 0 Learn
*/

run {
	some a : Arrival | {
		#a.packets.elems > 1
	}
} for 5 but  exactly 1 Learn, exactly 1 PacketMod, exactly 2 Switch, exactly 1 Output


pred packet_mod_changes_packet[] {
	some a: Arrival, pm: PacketMod | {
		a.packet.match != pm.new_match
	}
}

pred packet_mod_is_executed[] {
	some a: Arrival, pm: PacketMod | {
		pm in a.actions_executed.actions.elems
	}
}

show_packet_mod:
run {
	packet_mod_is_executed
	and packet_mod_changes_packet
} for 5 but exactly 1 Arrival, exactly 1 PacketMod, exactly 1 Output

-- We need to ensure that only learn actions can change switches
assert only_learn_changes {
	all e : Event | {
		all idx : e.exec_steps.inds - e.exec_steps.lastIdx | {
			let idx' = add[idx, 1] | {
				e.exec_steps[idx] != e.exec_steps[idx'] =>
					e.actions_executed.actions[idx] in Learn else
					e.actions_executed.actions[idx] not in Learn
			}
		}
	}
}

check only_learn_changes for 2 but 5 Int, exactly 1 Arrival, 5 Switch, exactly 1 Learn, 3 Match


assert only_packetmod_changes_packet {
	all a: Arrival | {
		all idx: a.packets.inds - a.packets.lastIdx | {
			let idx' = add[idx, 1] | {
					-- If the packets are different, we must have executed a PacketMod
					(a.packets[idx] != a.packets[idx']) implies 
						(a.actions_executed.actions[idx] in PacketMod)
					-- Alternate form that works with previous implementation:
					-- a.packets[idx].match != a.packets[idx'].match implies ...
			}
		}
	}
}
check only_packetmod_changes_packet for 5 but 5 Int, exactly 1 Arrival, 7 ActionList
