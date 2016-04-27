-- Things we need
-- - Multiple tables (via util/ordering)
-- - Packet events (arrival, timeout, skip)
-- - Actions (resubmit, output, learn, drop, increment, alert)
-- - Match criteria


-- Assertions/Properties
--  - Packets arrive at table 0
--  - Packets only get to subsequent tables if resubmitted to them
--  - If there are multiple matches, multiple action sets are executed
open util/ordering[Table_Id] as to
open util/ordering[Event] as eo

sig Switch {
	tables: Table_Id some -> one Table
} {
    Table_Id in tables.Table
}

sig Table_Id { }

sig Table {
  table_id: some Table_Id,
	rules: Rule
} 

sig Rule {
	match : one Match,
	action : seq Action,
 	timeout_actions: seq Action,
} {
	some action
}

sig Match {
}

lone sig CatchallMatch extends Match {}

abstract sig Action {
} {
  Action in Rule.action.elems
}

sig Resubmit extends Action {
	from: one Table_Id,
  to: one Table_Id
}

sig Output extends Action {
	-- Port?
}

sig Learn extends Action {
	table: one Table_Id,
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
fun learned_rules[actions: Action] : (Table_Id -> Rule) {
	{t : Table_Id, r : Rule | {
      some learn : (actions & Learn) | {
        t = learn.table
        r = learn.rule
      }
    }}

}

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
fun execute(p: Packet, s: Switch) : seq Action {
		
	let a = s.tables[to/first].rules.action | {
					a.append[s.tables[to/last].rules.action]
	}
}

// Get actions for one table (and tables to which it may resubmit)
/*
fun resubmit(m : Match , t: Table, s: Switch): seq Action {

}
*/
sig Arrival extends Event {
	packet: one Packet
} {
	actions_executed = execute[packet, pre.switch]
	--post.switch = pre.switch ++ learned_rules[actions_executed]
}

-- Timeouts can be nondeterministic for now
sig Timeout extends Event {
	rule: one Rule,
	table: one Table
} {
	-- Rule must be present in a switch table
	rule  in table.rules
	table in pre.switch.tables[Table_Id]

	actions_executed = rule.timeout_actions

	-- Warning:  might have issues if we learn the rule that timed out
	--post.switch = (pre.switch - (table -> rule)) ++ learned_rules[actions_executed]
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

-- Table IDs can't change between tables
fact table_id_matches_switch {
	all t: Table | {
		t.table_id = Switch.tables.t
	}
}

-- Resubmits must always go to a higher table_id
fact forward_resubmit {
    all s : Switch, t : Table | {
        t in s.tables[Table_Id] 
        (t.rules.action.elems & Resubmit).to in to/nexts[t.table_id]
    }
}

fact resubmit_from {
	all t: Table, r: Resubmit | {
			r in t.rules.action.elems implies (r.from = t.table_id)
	}
}

-- Facts
--  - Only new rules are added by learns
--  - 


-- Given a packet, find a match on the given tables

run {} for 2 but exactly 2 Table_Id


/*
 * TODO
 *   - Assert that resubmit's from is modeled accurately
 */



