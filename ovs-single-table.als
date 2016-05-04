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
	rule: Match one -> one ActionList
}

sig Drop extends Action {}
sig Alert extends Action {}


sig State {
	switch: one Switch,
}

abstract sig Event {
	pre, post: State,
	actions_executed: ActionList
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
fun execute[s: Switch, a: seq Action] : (one Switch) {
		
}
*/

/*
fun execute_learn[s: Switch, l: Learn] : (Switch) {
		switch.rules ++ l.rule
}
*/

fact one_catchall {
	one CatchallMatch
}

/*
-- Get new rules from a set of learn actions
fun learned_rules[actions: Action] : (Rule) {
	{ r : Rule | {
      some learn : (actions & Learn) | {
        r = learn.rule
      }
    }}
}
*/

-- Accumulate matches
-- ASSUMING RESUMBIT THROUGH ALL TABLES
-- Accumulate a sequence of actions from all tables where
-- Switch$0.tables[Table_Id$0].rules.match & p.math
/*
fun execute(p : Packet, s : Switch) : seq Action {
    switch.Table_Id
    -- switch.first's matching rule's actions + resubmit transitive closure's actions

  -- execute table 0,
  -- execute all actions in further tables
	
}
*/
// some mc : (p.match & r.match) | i -> a = mc.action
/*
fun get_matching_actions(p: Packet, r: Rule) : seq Action {
		{ i: Int, a : Action | some mc : (p.match & r.match) | i -> a = (r.mc).action }
}
*/

/* 
 * Why this is hard
 *   - Catchall match:  can't just take actions where match is equal,
 *                      need to take catchall rule if no other matches in a given table
 *   - Need to grab actions as a sequence and append them to a sequence
 *   - Need to take tables in order
 *   - Need to handle resubmits (and actions that may be added with them)
 *   - 
 */
/*
fun execute(p: Packet, s: Switch) : seq Action {
		
	let a = s.tables[to/first].rules.action | {
					a.append[s.tables[to/last].rules.action]
	}
}
*/

// Get actions for one table (and tables to which it may resubmit)
/*
fun resubmit(m : Match , t: Table, s: Switch): seq Action {

}
*/
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



