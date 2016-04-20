-- Things we need
-- - Multiple tables (via util/ordering)
-- - Packet events (arrival, timeout, skip)
-- - Actions (resubmit, output, learn, drop, increment, alert)
-- - Match criteria


-- Assertions/Properties
--  - Packets arrive at table 0
--  - Packets only get to subsequent tables if resubmitted to them
--  - If there are multiple matches, multiple action sets are executed
open util/ordering[Table] as to
open util/ordering[Event] as eo

sig Switch {
	tables: Table
}

sig Table {
	rules: Rule
}

sig Rule {
	match : one Match,
	action : some Action,
 	timeout_actions: Action,
}

sig Match {
}

lone sig CatchallMatch extends Match {}

abstract sig Action {
}

sig Resubmit extends Action {
  table: one Table
}

sig Output extends Action {
	-- Port?
}

sig Learn extends Action {
	table: one Table,
	rule: one Rule
}

sig Drop extends Action {}
sig Increment extends Action {}
sig Alert extends Action {}


sig State {
	switch: one Switch,
	ctr: Int
}

abstract sig Event {
	pre, post: State,
	actions_executed: seq Action
}



-- Get new rules from a set of learn actions
fun learned_rules[actions: Action] : (Table -> Rule) {
	let learns = (actions & Learn) | {
		all l : learns | {
      l.table -> l.rule
    }
	}
}

fun execute(p : Packet, s : Switch) : seq Action {

}

sig Arrival extends Event {
	packet: one Packet
} {
	actions_executed = execute[packet, pre.switch]
	post.switch = pre.switch ++ learned_rules[actions_executed]
}

-- Timeouts can be nondeterministic for now
sig Timeout extends Event {
	rule: one Rule,
	table: one Table
} {
	-- Rule must be present in a switch table
	rule  in table.rules
	table in pre.switch.tables

	actions_executed = rule.timeout_actions

	-- Warning:  might have issues if we learn the rule that timed out
	post.switch = (pre.switch - (table -> rule)) ++ learned_rules[actions_executed]
}



/*
-- Not required if we have non-deterministic timeouts
sig Tick extends Event {
} {
}
*/

sig Packet {
	match: one Match
}

-- Facts
--  - Only new rules are added by learns
--  - 


-- Given a packet, find a match on the given tables

run {} for 5




