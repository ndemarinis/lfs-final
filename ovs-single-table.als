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
}

sig Learn extends Action {
	rule: Match -> ActionList
} {
	#rule = 1
}

sig Drop extends Action {}
sig Alert extends Action {}


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

-- We only need to care about the learns
/*
pred execute[pre: Switch, post: Switch, a: ActionList] {
	all m: pre.rules.ActionList |
		let lastLearn = a.lastIdxOf[]
}
*/

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
	packet: one Packet
} {
	actions_executed = get_matching_actions[pre.switch, packet]
}


sig Packet {
	match: one Match
}

-- Facts
--  - Only new rules are added by learns
--  - 


-- Given a packet, find a match on the given tables

fact force_learn {
	some e: Event | {
		e.pre.switch != e.post.switch
	}
}

run {} for 2 but 5 Int, exactly 1 Arrival, 5 Switch, exactly 1 Learn

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

check only_learn_changes for 2 but 5 Int, exactly 1 Arrival, 5 Switch, exactly 1 Learn

/*
 * TODO
 *   - Assert that resubmit's from is modeled accurately
 */



