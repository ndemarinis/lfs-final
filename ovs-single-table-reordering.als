--
-- ovs-single-table-reordering.als
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

sig Match {}

lone sig CatchallMatch extends Match {}

fact one_catchall {
	one CatchallMatch
}


abstract sig Action {
} {
  Action in ActionList.actions.elems
}

sig Learn extends Action {
	rule: Match lone -> ActionList
} {
	one rule
}

sig Output extends Action {}

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

	-- Intermediate switch states for each stage of execution,
	-- with and without reordering
      	exec_steps_ideal:    seq Switch, -- Execution steps for executed_actions (ie, no reordering)
	exec_steps_permuted: seq Switch, -- Execution steps for permuted_actions

	-- Set of actions matched by this packet
	executed_actions: ActionList,   -- ActionList as given by the rule table (ie, no reordering)
        permuted_actions: ActionList,   -- Permuted action list (ie, with reordering)


} {
	-- We will have one more execution step than actions to execute
	#(exec_steps_permuted.inds) = add[#(permuted_actions.actions), 1]

	#exec_steps_ideal = #exec_steps_permuted

	exec_steps_permuted.first = pre.switch
	exec_steps_ideal.first    = pre.switch

	exec_steps_ideal.last = post.switch


	-- **** Reordering ****
	-- The matched actions must be a permutation of the actions that are executed
	is_permutation[permuted_actions.actions,
								 executed_actions.actions]

	-- For now, we can enforce that the actions MUST be reordered
	permuted_actions.actions != executed_actions.actions
}


sig Arrival extends Event {
	packet: one Packet
} {
	executed_actions = get_matching_actions[pre.switch, packet]
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

-- Execution steps without reordering
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

-- Given a switch (ie, a set of rules), find the ActionList matching
-- the given packet, or return the ActionList associated with the Switch's \
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

-- Execute a learn action by overriding a rule in the given switch
-- (if it exists) with the ActionList provided in the learn action.
-- If no action exists with the given match criteria, a new rule is installed.
fun execute_learn[s: Switch, l: Learn] : (Match -> ActionList) {
		s.rules ++ l.rule
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

-- ****** Examples and assertions *******

-- For visualization purposes, make sure we always execute a learn
-- NOTE:  Feel free to remove this or turn it into a pred.
fact force_learn {
	some e: Event | {
		e.pre.switch != e.post.switch
	}
}

-- Show an arbitrary instance where a learn is executed
run { } for 5 but 5 Int, exactly 1 Arrival, 5 Switch

-- Reordering had some effect on the output if the switch rules were
-- different at the end of the ideal and permuted execution steps.
pred reordering_affects_rules[e: Event] {
	e.exec_steps_ideal.last.rules != e.exec_steps_permuted.last.rules
}

-- Generate an instance where reordering has some effect on
-- the final rules for a switch after executing an event.
reordering_affects_rules:
run { some e: Event |
				reordering_affects_rules[e]
} for 5 but 5 Int, 5 Switch, 7 ActionList, exactly 1 Arrival


-- actions_are_swapped: True if a1 precedes a2 in the executed_actions,
--   but a2 preceeds a1 in the permuted_actions
pred actions_are_swapped[e: Event, a1: Action, a2 : Action] {
	e.executed_actions.actions.idxOf[a1] > e.executed_actions.actions.idxOf[a2] and
	e.permuted_actions.actions.idxOf[a1] < e.permuted_actions.actions.idxOf[a2]
}

-- If a reordering of learns had some effect on the
-- rule tables, there were some number of reordered learns that had
-- the same match criteria.
-- For all events:
--  If the reordering affects the rules:
--    For all disjoint Learns l1 & l2:
--	  If they are swapped between the regular list and permuted list
--        and they have the same match, but different action lists
--      Then
--        The final steps have different ActionLists for that match
-- Takeaway:  Ordering of learns with the same match criteria must be preserved in order to
--            not affect the final switch rules.
-- RUNTIME: Takes about 3 minutes to run
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

-- Only learn actions can change switch rule states
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
