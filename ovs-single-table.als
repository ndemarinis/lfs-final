--
-- ovs-single-table.als
-- This file provides a model for a single rule table
-- with execution of actions on packet events.
--

open util/ordering[Event] as eo

sig Switch {
	rules: Match -> lone ActionList
} {
	-- Switch rules must have at most
	-- one occurrence of each match atom
	#rules.ActionList = #rules
}


sig ActionList {
	actions: seq Action
} {
		some actions
}

sig Match {}

lone sig CatchallMatch extends Match {}

fact one_catchall {
	one CatchallMatch
}

abstract sig Action {
} {
  Action in ActionList.actions.elems
}

sig Output extends Action {}

sig Learn extends Action {
	rule: Match -> ActionList
} {
	one rule
}

sig Drop extends Action {}
sig Alert extends Action {}


sig State {
	switch: one Switch,
}

sig Packet {
	match: one Match
}

abstract sig Event {
  pre, post: State,

	-- Intermediate switch states for each stage of execution
  exec_steps: seq Switch,

	-- Set of executed actions for this event
	actions_executed: ActionList
} {
	-- We will have one more execution step than actions to execute
	#(exec_steps.inds) = add[#(actions_executed.actions.inds), 1]

	exec_steps.first = pre.switch
	exec_steps.last = post.switch
}

-- Packet arrival event
sig Arrival extends Event {
	packet: one Packet
} {
	actions_executed = get_matching_actions[pre.switch, packet]
}


fact transitions {
	all e: Event - eo/last | {
		let eNext = e.next | {
				e.post = eNext.pre
		}
	}
}

-- Define execution steps based on the matched actions
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

-- Given a switch (ie, a set of rules), find the ActionList matching
-- the given packet, or return the ActionList associated with the Switch's
-- CatchallMatch, if one exists
fun get_matching_actions[s: Switch, p: Packet] : (ActionList) {
		(p.match in s.rules.ActionList) =>
				s.rules[p.match]
		else { -- Table miss
				s.rules[CatchallMatch]
		}
}

-- Given a switch, return another switch with any changes
-- caused by learn actions
fun execute_if_learn[s: Switch, a: Action]: (Switch) {
		{ s2: Switch | {
			a in Learn =>
				s2.rules = execute_learn[s, (a :> Learn)] else
				s2.rules = s.rules
		}}
}

-- Given a switch, return another switch with any changes
-- caused by learn actions, optionally using the fields from the given packet
fun execute_learn[s: Switch, l: Learn] : (Match -> ActionList) {
		s.rules ++ l.rule
}


-- For visualization purposes, make sure we always execute a learn
-- NOTE:  Feel free to remove this or turn it into a pred.
fact learn_always_executed {
	some e: Event | {
		e.pre.switch != e.post.switch
	}
}

-- Show an arbitrary instance where a learn is executed
run {} for 5 but 5 Int, exactly 1 Arrival, 5 Switch

-- Make sure we only have one rule per match atom
assert only_single_match {
	all s: Switch | {
		-- If we only have at most one of each match,
		-- the size of set of all match criteria is equal to
		-- the number of rules
		#s.rules.ActionList = #s.rules
	}
}
check only_single_match for 5 but 5 Int, exactly 1 Arrival, 5 Switch


-- Only learn actions can change switch rule states
assert only_learn_changes {
	all e : Event | {
		all idx : e.exec_steps.inds - e.exec_steps.lastIdx | {
			let idx' = add[idx, 1] | {
				e.exec_steps[idx] != e.exec_steps[idx'] =>
					e.actions_executed.actions[idx] in Learn
			}
		}
	}
}

check only_learn_changes for 5 but 5 Int, exactly 1 Arrival, 5 Switch, exactly 1 Learn
