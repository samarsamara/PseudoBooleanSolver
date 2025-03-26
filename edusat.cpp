#include "PBSolver.h"
#include <algorithm>
#include <numeric>
#include <iostream>
#include <fstream>
#include <filesystem>
#include <string>

PBSolver S;

extern int verbose;
extern double begin_time;
extern double timeout;

using namespace std;

inline bool verbose_now() {
	return verbose > 1;
}



/******************  Reading the CNF ******************************/
#pragma region readCNF
void skipLine(ifstream& in) {
	for (;;) {
		//if (in.get() == EOF || in.get() == '\0') return;
		if (in.get() == '\n') { return; }
	}
}

static void skipWhitespace(ifstream& in, char& c) {
	c = in.get();
	while ((c >= 9 && c <= 13) || c == 32)
		c = in.get();
}

static int parseInt(ifstream& in) {
	int     val = 0;
	bool    neg = false;
	char c;
	skipWhitespace(in, c);
	if (c == '-') neg = true, c = in.get();
	if (c < '0' || c > '9') cout << c, Abort("Unexpected char in input", 1);
	while (c >= '0' && c <= '9')
		val = val * 10 + (c - '0'),
		c = in.get();
	return neg ? -val : val;
}


#pragma endregion readCNF


void PBSolver::read_pb(std::ifstream& in) {
	int vars = 0, constraints = 0;
	std::string line;

	// Process the header and comments until we get to constraints
	while (std::getline(in, line) && line[0] == '*') {
		std::cout << "Header/comment line: " << line << std::endl;

		// Extract variable and constraint counts from the line that has them
		if (line.find("#variable=") != std::string::npos) {
			// Format: "* #variable= 200 #constraint= 302 #product= 1248 sizeproduct= 2496"
			std::istringstream iss(line);
			std::string token;

			// Skip the '*'
			iss >> token; // This reads "*"

			// Read "#variable="
			iss >> token;
			if (token.find("#variable=") != std::string::npos) {
				// Read the value after "#variable="
				iss >> vars;
			}

			// Read "#constraint="
			iss >> token;
			if (token.find("#constraint=") != std::string::npos) {
				// Read the value after "#constraint="
				iss >> constraints;
			}

			std::cout << "Extracted: vars = " << vars << ", constraints = " << constraints << std::endl;
		}
	}

	// Check if we found valid variable and constraint counts
	if (vars <= 0 || constraints <= 0) {
		std::cerr << "Error: Could not extract valid variable and constraint counts" << std::endl;
		Abort("Invalid header information", 1);
	}

	set_nvars(vars);
	set_nconstraints(constraints);
	set_noldconstraints(constraints);
	initialize();

	std::cout << "Starting to read constraints...\n";

	// We'll process the current line (if it's not a comment) and then read more lines
	int constraint_index = 0;

	// Process the first non-comment line we already read
	if (!line.empty() && line[0] != '*' && line[0] != 'm') {
		processConstraint(line, constraint_index);
		constraint_index++;
	}
	/*&& constraint_index*/
	// Process remaining constraints
	while (std::getline(in, line) ) {
		if (line.empty() || line[0] == '*') {
			continue; // Skip empty lines and comments
		}

		processConstraint(line, constraint_index);
		constraint_index++;
	}

	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) reset_iterators();
	cout << "Read " << constraint_index << " constraints in " << cpuTime() - begin_time << " secs." << endl << "Solving..." << endl;
}

// Helper method to process a single constraint line
void PBSolver::processConstraint(const std::string& line, int& constraint_index) {
	Constraint c;
	size_t op_pos = std::string::npos;
	std::string constraint_op;

	// Find the constraint operator
	for (const std::string& op : { ">=", "<=", "=" }) {
		size_t temp_pos = line.find(op);
		if (temp_pos != std::string::npos && (op_pos == std::string::npos || temp_pos < op_pos)) {
			op_pos = temp_pos;
			constraint_op = op;
		}
	}

	if (op_pos == std::string::npos) {
		std::cout << "No operator found in constraint: " << line << std::endl;
		return;
	}

	// Get the RHS part (everything after the operator, up to semicolon or end)
	size_t semicolon_pos = line.find(';');
	std::string rhs_str = line.substr(op_pos + constraint_op.length(),
		(semicolon_pos != std::string::npos) ?
		semicolon_pos - (op_pos + constraint_op.length()) :
		std::string::npos);
	rhs_str = rhs_str.substr(0, rhs_str.find_first_of(";"));
	rhs_str = rhs_str.substr(rhs_str.find_first_not_of(" \t"));
	int rhs = std::stoi(rhs_str);

	// Get the LHS part (everything before the operator)
	std::string lhs_str = line.substr(0, op_pos);
	std::istringstream lhs_stream(lhs_str);

	// Process terms in the form "+1 x1" or "-1 x1 x2"
	std::string token;
	while (lhs_stream >> token) {
		// Check if token is a coefficient
		int coef;
		try {
			coef = std::stoi(token);
		}
		catch (std::invalid_argument&) {
			std::cout << "Invalid coefficient: " << token << std::endl;
			continue;
		}

		// Read variables following this coefficient
		std::vector<int> term_vars;
		while (lhs_stream.peek() == ' ' && lhs_stream >> token && token[0] == 'x') {
			int var;
			try {
				var = std::stoi(token.substr(1));
			}
			catch (std::invalid_argument&) {
				std::cout << "Invalid variable: " << token << std::endl;
				continue;
			}
			term_vars.push_back(var);
			// Register this variable with the constraint
			var_to_pb_constraints[var].push_back(constraint_index);
			var_occurrence_count[var]++;
		}

		// If token doesn't start with 'x', put it back in the stream
		if (!token.empty() && token[0] != 'x') {
			for (auto it = token.rbegin(); it != token.rend(); ++it) {
				lhs_stream.putback(*it);
			}
			lhs_stream.putback(' ');
		}

		// Handle the term based on number of variables
		if (term_vars.size() == 1) {
			c.insert_term(coef, term_vars[0]);
			if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) {
				bumpLitScore(v2l(term_vars[0]));
			}
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
				bumpVarScore(term_vars[0]);
			}
		}
		else if (term_vars.size() > 1) {
			c.insert_term(coef, term_vars[0]);
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
				bumpVarScore(term_vars[0]);
			}
			std::cout << "Simplified nonlinear term with " << term_vars.size() << " variables" << std::endl;
		}
	}

	// Set the right-hand-side value and initialize LHS to 0
	c.set_rhs(rhs);
	c.set_lhs(0);
	std::cout << "Constraint #" << constraint_index << " before normalization: ";
	c.print_constraint();

	// Normalize and add the constraint based on the operator.
	if (constraint_op == "=") {
		// For "=" split into two constraints.
		// Process the ≤ part:
		Constraint c_leq = c;
		normalizePBConstraint(c_leq, false); // normalize as ≤
		if (c_leq.constraint_size() == 1) {
			add_unary_constraint(c_leq);
			S.nconstraints += 1;
			S.noldconstraints += 1;
			std::cout << "After normalization (<=, unary): ";
			c_leq.print_constraint();
		}
		else if (c_leq.constraint_size() > 1) {
			add_constraint(c_leq, 0, 1);
			S.nconstraints += 1;
			S.noldconstraints += 1;
			std::cout << "After normalization (<=): ";
			c_leq.print_constraint();
		}

		// Process the ≥ part:
		Constraint c_geq = c;
		//constraint_index++;
		//std::vector<pair<int, int >> terms = c_geq.get_terms();
		//for (auto& term : terms ) {
		//	var_to_pb_constraints[term.second].push_back(constraint_index);
		//}
		normalizePBConstraint(c_geq, true);  // normalize as ≥
		if (c_geq.constraint_size() == 1) {
			add_unary_constraint(c_geq);
			std::cout << "After normalization (>=, unary): ";
			c_geq.print_constraint();
		}
		else if (c_geq.constraint_size() > 1) {
			add_constraint(c_geq, 0, 1);
			std::cout << "After normalization (>=): ";
			c_geq.print_constraint();
		}
	}
	else {
		// For ≥ or ≤, just normalize and add.
		if (constraint_op == ">=") {
			normalizePBConstraint(c, true);
		}
		else if (constraint_op == "<=") {
			normalizePBConstraint(c, false);
		}
		if (c.constraint_size() == 1) {
			add_unary_constraint(c);
			std::cout << "After normalization (unary): ";
			c.print_constraint();
		}
		else if (c.constraint_size() > 1) {
			add_constraint(c, 0, 1);
			std::cout << "After normalization: ";
			c.print_constraint();
		}
		else {
			std::cout << "Skipping empty constraint" << std::endl;
		}
	}
}


void PBSolver::add_constraint(Constraint& c, int l, int r) {
	Assert(c.constraint_size() > 1);
	c.lw_set(l);
	c.rw_set(r);
	int loc = static_cast<int>(pbConstraints.size());  // the first is in location 0 in cnf
	int size = c.constraint_size();
	if (c.get_rhs() < 0)
		unsat = true;
	//std::unordered_set<int> watches_set = findWatchesSet(c);
	//for (int lit : watches_set) {
	//	watches[lit].push_back(loc);
	//}
	//c.set_watches_set(watches_set);
	watches[c.lit(l)].push_back(loc);
	watches[c.lit(r)].push_back(loc);
	pbConstraints.push_back(c);
}


//debugging 
void PBSolver::print_variable_count(int var) {
	if (var_occurrence_count.find(var) == var_occurrence_count.end()) {
		std::cout << "Variable x" << var << " does not appear in any constraint.\n";
		return;
	}

	std::cout << "Variable x" << var << " appears " << var_occurrence_count[var] << " times across all constraints.\n";
}
/******************  Solving ******************************/
#pragma region solving

inline void PBSolver::reset_iterators(double where) {
	m_Score2Vars_it = (where == 0) ? m_Score2Vars.begin() : m_Score2Vars.lower_bound(where);
	Assert(m_Score2Vars_it != m_Score2Vars.end());
	m_VarsSameScore_it = m_Score2Vars_it->second.begin();
	m_should_reset_iterators = false;
}


void PBSolver::reset() { // invoked initially + every restart
	dl_pb = 0;
	max_dl = 0;
	conflicting_constraint_idx = -1;
	separators.push_back(0); // we want separators[1] to match dl=1. separators[0] is not used.
	conflicts_at_dl.push_back(0);
	pbConstraints.clear();
	var_to_pb_constraints.clear();
	var_occurrence_count.clear();
}

void PBSolver::initialize() {

	state_pb.resize(nvars + 1, VarState::V_UNASSIGNED);
	prev_state_pb.resize(nvars + 1, VarState::V_FALSE); // we set initial assignment with phase-saving to false. 
	antecedent.resize(nvars + 1, -1);
	marked.resize(nvars + 1);
	dlevel_pb.resize(nvars + 1);

	nlits = 2 * nvars;
	watches.resize(nlits + 1);
	LitScore.resize(nlits + 1);
	//initialize scores 	
	m_activity.resize(nvars + 1);
	m_curr_activity = 0.0f;
	for (unsigned int v = 0; v <= nvars; ++v) {
		m_activity[v] = 0;
	}
	reset();
}



int getCoefficient(const std::vector<std::pair<int, int>>& constraint, int var) {
	for (const auto& term : constraint) {
		if (term.second == var) {
			return term.first;  // Return coefficient if variable matches
		}
	}
	return 0; // Return 0 if the variable is not found
}


inline void PBSolver::assert_lit(Lit l) {
	if (l == 19) {
		std::cout << "19 \n";
	}
	trail_pb.push_back(l);
	int var = l2v(l);
	if (Neg(l)) prev_state_pb[var] = state_pb[var] = VarState::V_FALSE; else prev_state_pb[var] = state_pb[var] = VarState::V_TRUE;
	// Ensure we update all constraints where var appears
	for (int constraint_idx : var_to_pb_constraints[var]) {
		Constraint& pbc = pbConstraints[constraint_idx];
		int lhs = pbc.get_lhs();
		std::vector<std::pair<int, int>> terms = pbc.get_terms();

		for (auto& term : terms) {
			if (term.second == l) {
				lhs += term.first;
				pbc.set_lhs(lhs);
				break;
			}
		}
	}
	if (state_pb[var] == VarState::V_FALSE) std::cout << "false\n";
	dlevel_pb[var] = dl_pb;
	++num_assignments;
	if (verbose_now()) cout << l2rl(l) << " @ " << dl_pb << endl;
}

void PBSolver::m_rescaleScores(double& new_score) {
	if (verbose_now()) cout << "Rescale" << endl;
	new_score /= Rescale_threshold;
	for (unsigned int i = 1; i <= nvars; i++)
		m_activity[i] /= Rescale_threshold;
	m_var_inc /= Rescale_threshold;
	// rebuilding the scaled-down m_Score2Vars.
	map<double, unordered_set<Var>, greater<double>> tmp_map;
	double prev_score = 0.0f;
	for (auto m : m_Score2Vars) {
		double scaled_score = m.first / Rescale_threshold;
		if (scaled_score == prev_score) // This can happen due to rounding
			tmp_map[scaled_score].insert(m_Score2Vars[m.first].begin(), m_Score2Vars[m.first].end());
		else
			tmp_map[scaled_score] = m_Score2Vars[m.first];
		prev_score = scaled_score;
	}
	tmp_map.swap(m_Score2Vars);
}

void PBSolver::bumpVarScore(int var_idx) {
	double new_score;
	double score = m_activity[var_idx];

	if (score > 0) {
		Assert(m_Score2Vars.find(score) != m_Score2Vars.end());
		m_Score2Vars[score].erase(var_idx);
		if (m_Score2Vars[score].size() == 0) m_Score2Vars.erase(score);
	}
	new_score = score + m_var_inc;
	m_activity[var_idx] = new_score;

	// Rescaling, to avoid overflows; 
	if (new_score > Rescale_threshold) {
		m_rescaleScores(new_score);
	}

	if (m_Score2Vars.find(new_score) != m_Score2Vars.end())
		m_Score2Vars[new_score].insert(var_idx);
	else
		m_Score2Vars[new_score] = unordered_set<int>({ var_idx });
}

void PBSolver::bumpLitScore(int lit_idx) {
	LitScore[lit_idx]++;
}


void PBSolver::add_unary_constraint(Constraint c) {
	if (c.constraint_size() != 1) Abort("Unary constraint should have only one literal", 1);
	c.lw_set(0);
	c.rw_set(0);
	int loc = static_cast<int>(pbConstraints.size());  // the first is in location 0 in cnf

	watches[c.lit(0)].push_back(loc);
	pbConstraints.push_back(c);

}

int PBSolver::getVal(Var v) {
	switch (ValDecHeuristic) {
	case VAL_DEC_HEURISTIC::PHASESAVING: {
		VarState saved_phase = prev_state_pb[v];
		switch (saved_phase) {
		case VarState::V_FALSE:	return v2l(-v);
		case VarState::V_TRUE: return v2l(v);
		default: Assert(0);
		}
	}
	case VAL_DEC_HEURISTIC::LITSCORE:
	{
		int litp = v2l(v), litn = v2l(-v);
		int pScore = LitScore[litp], nScore = LitScore[litn];
		return pScore > nScore ? litp : litn;
	}
	default: Assert(0);
	}
	return 0;
}

SolverState PBSolver::decide() {
	if (verbose_now()) cout << "decide" << endl;
	Lit best_lit = 0;
	int max_score = 0;
	Var bestVar = 0;
	switch (VarDecHeuristic) {

	case  VAR_DEC_HEURISTIC::MINISAT: {
		// m_Score2Vars_r_it and m_VarsSameScore_it are fields. 
		// When we get here they are the location where we need to start looking. 		
		if (m_should_reset_iterators) reset_iterators(m_curr_activity);
		Var v = 0;
		int cnt = 0;
		if (m_Score2Vars_it == m_Score2Vars.end()) break;
		while (true) { // scores from high to low
			while (m_VarsSameScore_it != m_Score2Vars_it->second.end()) {
				v = *m_VarsSameScore_it;
				++m_VarsSameScore_it;
				++cnt;
				if (state_pb[v] == VarState::V_UNASSIGNED) { // found a var to assign
					m_curr_activity = m_Score2Vars_it->first;
					assert(m_curr_activity == m_activity[v]);
					best_lit = getVal(v);
					goto Apply_decision;
				}
			}
			++m_Score2Vars_it;
			if (m_Score2Vars_it == m_Score2Vars.end()) break;
			m_VarsSameScore_it = m_Score2Vars_it->second.begin();
		}
		break;
	}
	default: Assert(0);
	}

	assert(!best_lit);
	S.print_state(Assignment_file);
	return SolverState::SAT;


Apply_decision:
	dl_pb++; // increase decision level
	if (dl_pb > max_dl) {
		max_dl = dl_pb;
		separators.push_back(trail_pb.size());
		conflicts_at_dl.push_back(num_learned);
	}
	else {
		separators[dl_pb] = trail_pb.size();
		conflicts_at_dl[dl_pb] = num_learned;
	}

	assert_lit(best_lit);
	++num_decisions;
	asserted_lit = ::negate(best_lit);
	for (int constraint_idx : var_to_pb_constraints[l2v(best_lit)]) {
		Constraint& pbc = pbConstraints[constraint_idx];
		if (pbc.get_lhs() > pbc.get_rhs()) {
			conflicting_constraint_idx = constraint_idx;
			return SolverState::CONFLICT;
		}
	}

	return SolverState::UNDEF;
}

inline PBConstraintState Constraint::next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc) {
	if (verbose_now()) cout << "pb_next_not_false" << endl;


	// Constraint is SAT if LHS ≤ RHS
	if (lhs <= rhs)
		return PBConstraintState::PB_SAT;

	// Constraint is UNSAT if LHS > RHS (exceeds the allowed max)
	if (lhs > rhs) {
		if (verbose_now()) {
			PBConstraintState();
			cout << " is conflicting" << endl;
		}
		return PBConstraintState::PB_UNSAT;
	}

	// If clause is not binary, try to find another literal (other than other_watch) to watch.
	if (!binary) {
		for (size_t i = 0; i < literals.size(); ++i) {
			if (literals[i] == other_watch)
				continue;
			if (S.lit_state(literals[i]) != LitState::L_UNSAT) { // Found a candidate.
				loc = i;
				if (is_left_watch)
					lw = i;
				else
					rw = i;
				return PBConstraintState::PB_UNDEF; // No propagation; watch updated.
			}
		}
	}

	// No replacement found: Check if the other watched literal forces an implication.
	int coeff_other = -1;
	for (size_t i = 0; i < literals.size(); ++i) {
		if (literals[i] == other_watch) {
			coeff_other = coefficients[i];
			break;
		}
	}
	Assert(coeff_other != -1); // Must find other_watch in the clause.

	// Check if other_watch must be set to false to satisfy the constraint
	switch (S.lit_state(other_watch)) {
	case LitState::L_UNSAT:
		if (verbose_now()) {
			print_real_lits();
			cout << " is conflicting" << endl;
		}
		return PBConstraintState::PB_UNSAT;
	case LitState::L_UNASSIGNED:
		if (!other_watch || !binary)  // If setting other_watch to false is necessary
			return PBConstraintState::PB_UNIT;  // Must set other_watch = false
		return PBConstraintState::PB_UNDEF;  // Unresolved, keep watching
	case LitState::L_SAT:
		return PBConstraintState::PB_SAT;
	default:
		Assert(0);
		return PBConstraintState::PB_UNDEF;
	}
}


void PBSolver::test() { // tests that each clause is watched twice. 	
	for (unsigned int idx = 0; idx < pbConstraints.size(); ++idx) {
		Constraint c = pbConstraints[idx];
		bool found = false;
		for (int zo = 0; zo <= 1; ++zo) {
			for (vector<int>::iterator it = watches[c.get_literals()[zo]].begin(); !found && it != watches[c.get_literals()[zo]].end(); ++it) {
				if (*it == idx) {
					found = true;
					break;
				}
			}
		}
		if (!found) {
			cout << "idx = " << idx << endl;
			c.print_constraint();
			cout << endl;
			cout << c.constraint_size();
		}
		Assert(found);
	}
}

PBConstraintState PBSolver::propagate_assignment(int constraint_idx) {
	if (verbose_now()) cout << "propagate_assignment" << endl;

	Constraint c = pbConstraints[constraint_idx];

	clause_t literals = c.get_literals();
	std::vector<int> coefficients = c.get_coefficients();
	int rhs = c.get_rhs();
	int lhs = c.get_lhs();
	int remaning_slack = rhs - lhs;
	int true_sum = 0;


	if (remaning_slack < 0) return PBConstraintState::PB_UNSAT;
	for (int i = 0; i < c.constraint_size(); ++i) {
		if (S.lit_state(literals[i]) == LitState::L_UNASSIGNED && coefficients[i] > remaning_slack) {
			assert_lit(negate(literals[i]));
			antecedent[l2v(literals[i])] = constraint_idx;

		}
	}
	if (remaning_slack >= 0) return  PBConstraintState::PB_SAT;
	return  PBConstraintState::PB_UNDEF;
}

SolverState PBSolver::BCP() {

	if (verbose_now()) cout << "BCP" << endl;
	if (verbose_now()) cout << "qhead = " << qhead << " trail-size = " << trail_pb.size() << endl;

	if (unsat)
		return SolverState::UNSAT;

	while (qhead < trail_pb.size()) {
		Lit lit = trail_pb[qhead];
		int var = l2v(lit);
		Lit NegatedLit = ::negate(trail_pb[qhead++]);
		Assert(lit_state(NegatedLit) == LitState::L_UNSAT);
		if (verbose_now()) cout << "propagating " << l2rl(::negate(NegatedLit)) << endl;

		for (int constraint_idx : var_to_pb_constraints[var]) {
			PBConstraintState res = propagate_assignment(constraint_idx);
			switch (res) {
				case PBConstraintState::PB_UNSAT: { // conflict				
					if (verbose_now()) print_state();
					if (dl_pb == 0 || unsat) return SolverState::UNSAT;
					conflicting_constraint_idx = constraint_idx;  // this will also break the loop
					if (verbose_now()) cout << "conflict" << endl;
					return SolverState::CONFLICT;
				}
				case PBConstraintState::PB_SAT:
					if (verbose_now()) cout << "constraint is sat" << endl;
					break; // nothing to do when clause has a satisfied literal.
				case PBConstraintState::PB_UNIT: { // new implication				
					break;
				}
				default: // replacing watch_lit
					break;
				}
			}

		}
		return SolverState::UNDEF;
	}



/*******************************************************************************************************************
name: analyze
input:	1) conflicting clause
		2) dlevel
		3) marked

assumes: 1) no clause should have the same literal twice. To guarantee this we read through a set in read_cnf.
			Wihtout this assumption it may loop forever because we may remove only one copy of the pivot.

This is Alg. 1 from "HaifaSat: a SAT solver based on an Abstraction/Refinement model"
********************************************************************************************************************/

int PBSolver::analyze(const Constraint& conflictConstraint) {
	if (verbose_now()) cout << "PB Conflict Analysis" << endl;

	Constraint new_constraint;
	int resolve_num = 0, bktrk = 0, watch_lit = 0;
	Lit u;
	Var v;

	// Step 1: Compute a Minimal Conflict Subset
	Constraint learned_constraint = findConflictSubset(conflictConstraint);

	// Step 2: Extract Variables from the Conflict Clause
	for (auto& term : learned_constraint.get_terms()) {
		Lit lit = term.second;  // This is already a literal
		v = l2v(lit);           // Convert to variable for tracking
		var_to_pb_constraints[v].push_back(pbConstraints.size());
		if (!marked[v]) {
			marked[v] = true;
			if (dlevel_pb[v] == dl_pb) ++resolve_num;
			else {
				new_constraint.insert_term(term.first, lit);  // Keep the original literal
				int c_dl = dlevel_pb[v];
				if (c_dl > bktrk) {
					bktrk = c_dl;
					watch_lit = new_constraint.constraint_size() - 1;
				}
			}
		}
	}

	// Step 3: Learn a New PB Constraint
	if (learned_constraint.constraint_size() == 1)
		add_unary_constraint(learned_constraint);
	else
		add_constraint(learned_constraint, 0, 1);
	nconstraints++;
	num_learned++;

	if (verbose_now()) {
		cout << "Learned PB Constraint: ";
		learned_constraint.print_constraint();
	}

	return bktrk;
}

void PBSolver::backtrack(int k) {
	if (verbose_now()) cout << "backtrack" << endl;
	// local restart means that we restart if the number of conflicts learned in this 
	// decision level has passed the threshold. 
	if (k > 0 && (num_learned - conflicts_at_dl[k] > restart_threshold)) {	// "local restart"	
		restart();
		return;
	}
	static int counter = 0;

	for (trail_t::iterator it = trail_pb.begin() + separators[k + 1]; it != trail_pb.end(); ++it) { // erasing from k+1
		Var v = l2v(*it);
		if (dlevel_pb[v]) { // we need the condition because of learnt unary clauses. In that case we enforce an assignment with dlevel = 0.
			state_pb[v] = VarState::V_UNASSIGNED;
			antecedent[v] = -1;
			for (int constraint_idx : var_to_pb_constraints[v]) {
				if (constraint_idx >= noldconstraints) continue; // we do not want to backtrack on the learned constraints.
				Constraint& pbc = pbConstraints[constraint_idx];
				int lhs = pbc.get_lhs();
				if (pbc.get_rhs() == 0)
					continue;
				std::vector<std::pair<int, int>> terms = pbc.get_terms();
				for (auto& term : terms) {
					if (term.second == *it) {
						lhs -= term.first;
						pbc.set_lhs(lhs);
						break;
					}
				}
			}

			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_curr_activity = max(m_curr_activity, m_activity[v]);
		}
	}
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_should_reset_iterators = true;
	if (verbose_now()) print_state();
	trail_pb.erase(trail_pb.begin() + separators[k + 1], trail_pb.end());
	qhead = trail_pb.size();
	dl_pb = k;
	if (dl_pb == 0)
		std::cout << "lll" ;
	assert_lit(asserted_lit);
	for (size_t i = 0; i < noldconstraints; ++i) {
		Constraint& c = pbConstraints[i];
		if (std::find(watches[c.get_lw_lit()].begin(), watches[c.get_lw_lit()].end(), i) == watches[c.get_lw_lit()].end()) {
			watches[c.get_lw_lit()].push_back(i);
		}
		if (std::find(watches[c.get_rw_lit()].begin(), watches[c.get_rw_lit()].end(), i) == watches[c.get_rw_lit()].end()) {
			watches[c.get_rw_lit()].push_back(i);
		}
	}
	set_noldconstraints(pbConstraints.size());
	antecedent[l2v(asserted_lit)] = pbConstraints.size() - 1;
	conflicting_constraint_idx = -1;
}

void PBSolver::validate_assignment() {
	if (num_assignments < nvars)
		for (unsigned int i = 1; i <= nvars; ++i) if (state_pb[i] == VarState::V_UNASSIGNED) {
			cout << "Unassigned var: " + to_string(i) << endl; // This is supposed to happen only if the variable does not appear in any clause
		}
	for (auto it = pbConstraints.begin(); it != pbConstraints.end(); ++it) {
		if (it->get_lhs() > it->get_rhs()) {
			cout << "fail on constraint: ";
			it->print_constraint();
			cout << endl;
			for (clause_it it_c = it->get_literals().begin(); it_c != it->get_literals().end(); ++it_c)
				cout << *it_c << " (" << (int)lit_state(*it_c) << ") ";
			cout << endl;
			Abort("Assignment validation failed", 3);
		}
	}
	for (auto it = unaries.begin(); it != unaries.end(); ++it) {
		Lit lit = it->get_literals()[0];
		if (it->get_lhs() > it->get_rhs())
			Abort("Assignment validation failed (unaries)", 3);
	}
	cout << "Assignment validated" << endl;
}



void PBSolver::restart() {
	if (verbose_now()) cout << "restart" << endl;
	restart_threshold = static_cast<int>(restart_threshold * restart_multiplier);
	if (restart_threshold > restart_upper) {
		restart_threshold = restart_lower;
		restart_upper = static_cast<int>(restart_upper * restart_multiplier);
		if (verbose >= 1) cout << "new restart upper bound = " << restart_upper << endl;
	}
	if (verbose >= 1) cout << "restart: new threshold = " << restart_threshold << endl;
	++num_restarts;
	for (unsigned int i = 1; i <= nvars; ++i)
		if (dlevel_pb[i] > 0) {
			state_pb[i] = VarState::V_UNASSIGNED;
			dlevel_pb[i] = 0;
		}
	trail_pb.clear();
	qhead = 0;
	separators.clear();
	conflicts_at_dl.clear();
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
		m_curr_activity = 0; // The activity does not really become 0. When it is reset in decide() it becomes the largets activity. 
		m_should_reset_iterators = true;
	}
	reset();
}

void PBSolver::solve() {
	SolverState res = _solve();
	Assert(res == SolverState::SAT || res == SolverState::UNSAT || res == SolverState::TIMEOUT);
	S.print_stats();
	switch (res) {
	case SolverState::SAT: {
		S.validate_assignment();
		string str = "solution in ",
			str1 = Assignment_file;
		cout << str + str1 << endl;
		cout << "SAT" << endl;
		break;
	}
	case SolverState::UNSAT:
		cout << "UNSAT" << endl;
		break;
	case SolverState::TIMEOUT:
		cout << "TIMEOUT" << endl;
		return;
	}
	return;
}

SolverState PBSolver::_solve() {
	SolverState res;
	while (true) {
		if (timeout > 0 && cpuTime() - begin_time > timeout) return SolverState::TIMEOUT;
		while (true) {
			res = BCP();
			if (res == SolverState::UNSAT) return res;
			if (res == SolverState::CONFLICT)
			{
				cout << "CONFLICT" << endl;
				int bktrk = analyze(pbConstraints[conflicting_constraint_idx]);
				backtrack(bktrk);
			}
			else
				break;
		}
		res = decide();
		if (res == SolverState::SAT) return res;
	}
}

void PBSolver::normalizePBConstraint(Constraint& pb_constraint, bool bigger) {
	Constraint newConstraint;
	std::vector<pair<int, int >> terms = pb_constraint.get_terms();
	int rhs = pb_constraint.get_rhs();
	//Step 1: Flip inequality if RHS is negative
	if (bigger) {
		rhs *= -1;  // Convert RHS to positive
		for (auto& term : terms) {
			term.first *= -1;  // Multiply coefficients by -1
		}
	}

	//Step 2: Convert each term correctly
	pb_constraint.reset_terms();
	pb_constraint.reset_coefficients();
	pb_constraint.reset_literals();
	for (auto& term : terms) {
		int coeff = term.first;
		int var = term.second;

		if (coeff < 0) {
			//Apply transformation: x_i = 1 - x̅_i
			coeff = -coeff;
			rhs += coeff;  // Adjust RHS by subtracting the negated term
			var = v2l(-var);
		}
		else var = v2l(var);
		pb_constraint.insert_term(coeff, var);
		pb_constraint.set_rhs(rhs);
	}
	std::cout << "RHS after normalization " << " " << pb_constraint.get_rhs() << "\n";


}


Constraint PBSolver::findConflictSubset(Constraint constraint) {
	Constraint conflictConstraint;
	int accumulated_sum = 0;
	int rhs = constraint.get_rhs();
	int rhs_c = 0;

	std::cout << "Finding minimal conflict set for Constraint with RHS: " << rhs << "\n";

	// Sort terms by coefficient value (highest first)
	std::vector<std::pair<int, int>> sorted_terms = constraint.get_terms();
	std::sort(sorted_terms.begin(), sorted_terms.end(), [](auto& a, auto& b) {
		return abs(a.first) > abs(b.first);
		});

	// Add literals contributing to the conflict
	for (const auto& term : sorted_terms) {
		int coeff = term.first;
		int lit = term.second;  // This is already a literal (doubled index)
		int var = l2v(lit);     // Get the variable from the literal

		// Check if this variable contributes to the conflict based on its assignment
		if ((state_pb[var] == VarState::V_TRUE && !Neg(lit)) ||
			(state_pb[var] == VarState::V_FALSE && Neg(lit))) {

			// Add this term to the conflict constraint (with coefficient 1)
			conflictConstraint.insert_term(1, lit);  // Keep the original literal
			accumulated_sum += coeff;
			rhs_c += 1;

			std::cout << "Adding x" << lit << "\n";

			// Stop once we've found enough terms to explain the conflict
			if (accumulated_sum > rhs) {
				break;
			}
		}
	}

	// Set the RHS of the conflict constraint
	conflictConstraint.set_rhs(rhs_c - 1);

	std::cout << "Learned PB Conflict Constraint: ";
	for (const auto& term : conflictConstraint.get_terms()) {
		std::cout << term.first << "x" << term.second << " ";
	}
	std::cout << "<= " << conflictConstraint.get_rhs() << "\n";

	return conflictConstraint;
}


#pragma endregion solving




/******************  main ******************************/

int main(int argc, char** argv) {
	begin_time = cpuTime();
	parse_options(argc, argv);

	std::ifstream file("normalized-dbst_v30_e350_d15_mw10_1.opb.PB06.opb");
	/*std::ifstream file("normalized-air01.0.s.opb"); */ // SAT
	//std::ifstream file("normalized-blast-floppy1-8.ucl.opb"); //UNSAT
	//std::ifstream file("normalized-fpga11_10_sat_pb.cnf.cr.opb"); //SAT
	//std::ifstream file("normalized-grid4_81.opb"); // UNSAT
	S.read_pb(file);
	file.close();
	S.solve();

	return 0;
}
