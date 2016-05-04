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
	#(exec_steps.inds) = #(actions_executed.actions.inds) -- Should there be 1 more exec_step than actions?
	exec_steps.first = pre.switch
	exec_steps.last = post.switch
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
		{ss: Switch | some s2: Switch | { 
						s2.rules = ((a in Learn) => {
													execute_learn[s, (a :> Learn)] 
												} else { 
														s.rules
												})
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

	--actions_executed = execute[packet, pre.switch]
	--post.switch = pre.switch ++ learned_rules[actions_executed]
}


sig Packet {
	match: one Match
}

-- Facts
--  - Only new rules are added by learns
--  - 


-- Given a packet, find a match on the given tables

run {} for 2 but 5 Int


/*
 * TODO
 *   - Assert that resubmit's from is modeled accurately
 */



