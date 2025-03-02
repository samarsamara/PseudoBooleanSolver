#include "PBSolver.h"
#include <algorithm>
#include <numeric>

PBSolver S;

using namespace std;

inline bool verbose_now() {
	return verbose > 1;
}


//int Solver::create_variable() {
//	return ++variable_count; // Increment and return a new variable index
//}
//
//
//std::vector<Clause> Solver::convert_pb_to_cnf(const std::vector<std::pair<int, int>>& terms, int rhs) {
//	std::vector<Clause> cnf_clauses;
//
//	// Step 1: Initialize buckets
//	int max_bits = 0;
//	for (const auto& term : terms) {
//		int coeff = term.first;
//		while (coeff > 0) {
//			coeff >>= 1;
//			max_bits++;
//		}
//	}
//	std::vector<std::vector<int>> buckets(max_bits);
//
//	// Step 2: Fill the buckets
//	for (const auto& term : terms) {
//		int coeff = term.first; // Coefficient
//		create_variable();
//		int var = term.second;  // Variable
//		int bit_position = 0;
//
//		while (coeff > 0) {
//			if (coeff & 1) {
//				buckets[bit_position].push_back(var);
//			}
//			coeff >>= 1;
//			bit_position++;
//		}
//	}
//
//	// Step 3: Build the adder tree
//    for (size_t i = 0; i < buckets.size(); ++i) {
//		std::cout << i << std::endl;
//		print_buckets(buckets);
//		while (buckets[i].size() >= 3) {
//			int a = buckets[i].back(); buckets[i].pop_back();
//			int b = buckets[i].back(); buckets[i].pop_back();
//			int c = buckets[i].back(); buckets[i].pop_back();
//
//			int sum = create_variable();
//			int carry = create_variable();
//
//			cnf_clauses = add_full_adder_clauses(a, b, c, sum, carry);
//
//			buckets[i + 1].push_back(carry);
//			buckets[i].push_back(sum);
//		}
//
//		if (buckets[i].size() == 2) {
//			int a = buckets[i].back(); buckets[i].pop_back();
//			int b = buckets[i].back(); buckets[i].pop_back();
//
//			int sum = create_variable();
//			int carry = create_variable();
//
//			add_half_adder_clauses(a, b, sum, carry);
//
//			buckets[i + 1].push_back(carry);
//			buckets[i].push_back(sum);
//		}
//	}
//
//	// Step 4: Enforce RHS constraint
//    for (size_t i = rhs + 1; i < buckets.size(); ++i) {
//		for (int bit : buckets[i]) {
//			Clause c;
//			c.insert(-bit); // Negate the bit
//			cnf_clauses.push_back(c);
//		}
//	}
//
//	return cnf_clauses;
//}
//
//std::vector<Clause> Solver::add_full_adder_clauses(int a, int b, int c_in, int sum, int c_out) {
//	// Sum bit clauses
//	std::vector<Clause> clauses;
//	Clause c1; // ¬a ∨ ¬b ∨ ¬c_in ∨ s
//	c1.insert(-a);
//	c1.insert(-b);
//	c1.insert(-c_in);
//	c1.insert(sum);
//	clauses.push_back(c1);
//
//	Clause c2; // a ∨ b ∨ ¬s
//	c2.insert(a);
//	c2.insert(b);
//	c2.insert(-sum);
//	clauses.push_back(c2);
//
//	Clause c3; // b ∨ c_in ∨ ¬s
//	c3.insert(b);
//	c3.insert(c_in);
//	c3.insert(-sum);
//	clauses.push_back(c3);
//
//	Clause c4; // c_in ∨ a ∨ ¬s
//	c4.insert(c_in);
//	c4.insert(a);
//	c4.insert(-sum);
//	clauses.push_back(c4);
//
//	// Carry-out bit clauses
//	Clause c5; // ¬a ∨ ¬b ∨ c_out
//	c5.insert(-a);
//	c5.insert(-b);
//	c5.insert(c_out);
//	clauses.push_back(c5);
//
//	Clause c6; // ¬b ∨ ¬c_in ∨ c_out
//	c6.insert(-b);
//	c6.insert(-c_in);
//	c6.insert(c_out);
//	clauses.push_back(c6);
//
//	Clause c7; // ¬c_in ∨ ¬a ∨ c_out
//	c7.insert(-c_in);
//	c7.insert(-a);
//	c7.insert(c_out);
//	clauses.push_back(c7);
//
//	Clause c8; // a ∨ ¬c_out
//	c8.insert(a);
//	c8.insert(-c_out);
//	clauses.push_back(c8);
//
//	Clause c9; // b ∨ ¬c_out
//	c9.insert(b);
//	c9.insert(-c_out);
//	clauses.push_back(c9);
//
//	Clause c10; // c_in ∨ ¬c_out
//	c10.insert(c_in);
//	c10.insert(-c_out);
//	clauses.push_back(c10);
//	return clauses;
//
//}
//
//std::vector<Clause> Solver::add_half_adder_clauses(int a, int b, int sum, int c_out) {
//	std::vector<Clause> clauses;
//	// Sum bit clauses
//	Clause c1; //  ¬a ∨ ¬b ∨ s
//	c1.insert(-a);
//	c1.insert(-b);
//	c1.insert(sum);
//	clauses.push_back(c1);
//
//	Clause c2; //  a ∨ b ∨ ¬s
//	c2.insert(a);
//	c2.insert(b);
//	c2.insert(-sum);
//	clauses.push_back(c2);
//
//	// Carry-out bit clauses
//	Clause c3; // ¬a ∨ ¬b ∨ c_out
//	c3.insert(-a);
//	c3.insert(-b);
//	c3.insert(-c_out);
//	clauses.push_back(c3);
//
//	Clause c4; // a ∨ ¬c_out
//	c4.insert(a);
//	c4.insert(-c_out);
//	clauses.push_back(c4);
//
//	Clause c5; // b ∨ ¬c_out
//	c5.insert(b);
//	c5.insert(-c_out);
//	clauses.push_back(c5);
//	return clauses;
//}


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

//void Solver::read_cnf(ifstream& in) {
//	int i;
//	unsigned int vars, clauses, unary = 0;
//	set<Lit> s;
//	Clause c;
//
//
//	while (in.peek() == 'c') skipLine(in);
//
//	if (!match(in, "p cnf")) Abort("Expecting `p cnf' in the beginning of the input file", 1);
//	in >> vars; // since vars is int, it reads int from the stream.
//	in >> clauses;
//	if (!vars || !clauses) Abort("Expecting non-zero variables and clauses", 1);
//	cout << "vars: " << vars << " clauses: " << clauses << endl;
//	cnf.reserve(clauses);
//
//	set_nvars(vars);
//	set_nclauses(clauses);
//	initialize();
//
//	while (in.good() && in.peek() != EOF) {
//		i = parseInt(in);
//		if (i == 0) {
//			c.cl().resize(s.size());
//			copy(s.begin(), s.end(), c.cl().begin());
//			switch (c.size()) {
//			case 0: {
//				stringstream num;  // this allows to convert int to string
//				num << cnf_size() + 1; // converting int to string.
//				Abort("Empty clause not allowed in input formula (clause " + num.str() + ")", 1); // concatenating strings
//			}
//			case 1: {
//				Lit l = c.cl()[0];
//				// checking if we have conflicting unaries. Sufficiently rare to check it here rather than 
//				// add a check in BCP. 
//				if (state[l2v(l)] != VarState::V_UNASSIGNED)
//					if (Neg(l) != (state[l2v(l)] == VarState::V_FALSE)) {
//						S.print_stats();
//						Abort("UNSAT (conflicting unaries for var " + to_string(l2v(l)) + ")", 0);
//					}
//				assert_lit(l);
//				add_unary_clause(l);
//				break; // unary clause. Note we do not add it as a clause. 
//			}
//			default: add_clause(c, 0, 1);
//			}
//			c.reset();
//			s.clear();
//			continue;
//		}
//		if (Abs(i) > vars) Abort("Literal index larger than declared on the first line", 1);
//		if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(abs(i));
//		i = v2l(i);
//		if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(i);
//		s.insert(i);
//	}
//	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) reset_iterators();
//	cout << "Read " << cnf_size() << " clauses in " << cpuTime() - begin_time << " secs." << endl << "Solving..." << endl;
//}
//
#pragma endregion readCNF


void PBSolver::read_pb(std::ifstream& in) {
	int vars, constraints;

	if (!match(in, "* #variable=")) Abort("Expecting `*' in the input file", 1);
	in >> vars;
	if (!match(in, " #constraint=")) Abort("No constraints provided", 1);
	in >> constraints;

	std::cout << "constraints size = " << constraints << "\n";
	std::cout << "nvars  = " << vars << "\n";

	set_nvars(vars);
	set_nconstraints(constraints);
	initialize();

	// Ensure we skip any remaining characters on the current line
	in.ignore(std::numeric_limits<std::streamsize>::max(), '\n');


	//while (in.good() && in.peek() != '*') in.get();
	//while (in.good() && in.peek() == '*') skipLine(in);


	std::cout << "Starting to read constraints...\n";

	// Read process the constraints
	std::string token1, token2;
	int coef, lit, rhs;
	int i = 0;

	Constraint c;

	while (in.good() && in.peek() != EOF) {
		in >> token1 >> token2;
		// cout << token1 << token2 << endl;
		if (token1 == ">=" || token2 == "=" || token1 == "<=") {
			// end of constraint
			if (token1 != ">=" && token1 != "<=") Abort("only >= or <= is supported", 1);
			rhs = std::stoi(token2);
			c.set_rhs(rhs);
			std::cout << "constraint before normalization \n";
			c.print_constraint();
			if(token1 == ">=")
				normalizePBConstraint(c, true);
			else
				normalizePBConstraint(c, false);
			add_constraint(c, 0, 1);
			c.print_constraint();
			i++;
			c.reset_coefficients();
			c.reset_literals();
			c.reset_terms();

		}
		else {
			coef = std::stoi(token1);
			lit = std::stoi(token2.substr(1));

			if (lit > vars) Abort("Literal index larger than declared on the first line", 1);
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(lit);

			c.insert_term(coef, lit);
			var_to_pb_constraints[lit].push_back(i);
			var_occurrence_count[lit]++;

			if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(v2l(lit));
		}
	}
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) reset_iterators();
	cout << "Read " << constraints << " constraints in " << cpuTime() - begin_time << " secs." << endl << "Solving..." << endl;
}



void PBSolver::add_constraint(Constraint& c, int l, int r) {
	Assert(c.constraint_size() > 1);
	c.lw_set(l);
	c.rw_set(r);
	int loc = static_cast<int>(pbConstraints.size());  // the first is in location 0 in cnf
	int size = c.constraint_size();

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
	unaries.push_back(c);
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
	for (int constraint_idx : var_to_pb_constraints[l2v(best_lit)]) {
		Constraint& pbc = pbConstraints[constraint_idx];
		if (pbc.get_lhs() > pbc.get_rhs()) {
			asserted_lit = negate(best_lit);
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

	// Check if `other_watch` must be set to false to satisfy the constraint
	switch (S.lit_state(other_watch)) {
	case LitState::L_UNSAT:
		if (verbose_now()) {
			print_real_lits();
			cout << " is conflicting" << endl;
		}
		return PBConstraintState::PB_UNSAT;
	case LitState::L_UNASSIGNED:
		if ((lhs + coeff_other) > rhs)  // If setting `other_watch` to false is necessary
			return PBConstraintState::PB_UNIT;  // Must set `other_watch = false`
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

SolverState PBSolver::BCP() {

	if (verbose_now()) cout << "BCP" << endl;
	if (verbose_now()) cout << "qhead = " << qhead << " trail-size = " << trail_pb.size() << endl;
	
	while (qhead < trail_pb.size()) {
		Lit NegatedLit = negate(trail_pb[qhead++]);
		Assert(lit_state(NegatedLit) == LitState::L_UNSAT);
		if (verbose_now()) cout << "propagating " << l2rl(negate(NegatedLit)) << endl;

		vector<int> new_watch_list; // The original watch list minus those clauses that changed a watch. The order is maintained. 
		int new_watch_list_idx = watches[NegatedLit].size() - 1; // Since we are traversing the watch_list backwards, this index goes down.
		new_watch_list.resize(watches[NegatedLit].size());


		for (vector<int>::reverse_iterator it = watches[NegatedLit].rbegin(); it != watches[NegatedLit].rend() && conflicting_constraint_idx < 0; ++it) {
			Constraint& c = pbConstraints[*it];
			Lit l_watch = c.get_lw_lit(),
				r_watch = c.get_rw_lit();
			bool binary = c.constraint_size() == 2;
			bool is_left_watch = (l_watch == NegatedLit);
			Lit other_watch = is_left_watch ? r_watch : l_watch;
			int NewWatchLocation;
			PBConstraintState res = c.next_not_false(is_left_watch, other_watch, binary, NewWatchLocation);
			if (res != PBConstraintState::PB_UNDEF) new_watch_list[new_watch_list_idx--] = *it; //in all cases but the move-watch_lit case we leave watch_lit where it is
			switch (res) {
			case PBConstraintState::PB_UNSAT: { // conflict				
				if (verbose_now()) print_state();
				if (dl_pb == 0) return SolverState::UNSAT;
				conflicting_constraint_idx = *it;  // this will also break the loop
				int dist = distance(it, watches[NegatedLit].rend()) - 1; // # of entries in watches[NegatedLit] that were not yet processed when we hit this conflict. 
				// Copying the remaining watched clauses:
				for (int i = dist - 1; i >= 0; i--) {
					new_watch_list[new_watch_list_idx--] = watches[NegatedLit][i];
				}
				if (verbose_now()) cout << "conflict" << endl;
				break;
			}
			case PBConstraintState::PB_SAT:
				if (verbose_now()) cout << "constraint is sat" << endl;
				break; // nothing to do when clause has a satisfied literal.
			case PBConstraintState::PB_UNIT: { // new implication				
				if (verbose_now()) cout << "propagating: ";
				assert_lit(other_watch);
				antecedent[l2v(other_watch)] = *it;
				if (verbose_now()) cout << "new implication <- " << l2rl(other_watch) << endl;
				break;
			}
			default: // replacing watch_lit
				Assert(NewWatchLocation < static_cast<int>(c.constraint_size()));
				int new_lit = c.lit(NewWatchLocation);
				watches[new_lit].push_back(*it);
				if (verbose_now()) { c.print_real_lits(); cout << " now watched by " << l2rl(new_lit) << endl; }
			}
		}
		// resetting the list of clauses watched by this literal.
		watches[NegatedLit].clear();
		new_watch_list_idx++; // just because of the redundant '--' at the end. 		
		watches[NegatedLit].insert(watches[NegatedLit].begin(), new_watch_list.begin() + new_watch_list_idx, new_watch_list.end());

		//print_watches();
		if (conflicting_constraint_idx >= 0) return SolverState::CONFLICT;
		new_watch_list.clear();
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

	// 🔹 Step 1: Compute a Minimal Conflict Subset
	Constraint learned_constraint = findConflictSubset(conflictConstraint);

	// 🔹 Step 2: Extract Variables from the Conflict Clause
	for (auto& term : learned_constraint.get_terms()) {
		Lit lit = v2l(term.second);
		v = l2v(lit);

		if (!marked[v]) {
			marked[v] = true;
			if (dlevel_pb[v] == dl_pb) ++resolve_num;
			else {
				new_constraint.insert_term(term.first, term.second);
				int c_dl = dlevel_pb[v];
				if (c_dl > bktrk) {
					bktrk = c_dl;
					watch_lit = new_constraint.constraint_size() - 1;
				}
			}
		}
	}


	// 🔹 Step 3: Learn a New PB Constraint
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
			for (int constraint_idx : var_to_pb_constraints[v]) {
				Constraint& pbc = pbConstraints[constraint_idx];
				int lhs = pbc.get_lhs();
				std::vector<std::pair<int, int>> terms = pbc.get_terms();

				for (auto& term : terms) {
					if (term.second == *it){
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
	assert_lit(asserted_lit);
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
			for (clause_it it_c = it->get_literals().begin(); it_c != it->get_literals().end() ; ++it_c)
				cout << *it_c << " (" << (int)lit_state(*it_c) << ") ";
			cout << endl;
			Abort("Assignment validation failed", 3);
		}
	}
	for (auto it = unaries.begin(); it != unaries.end(); ++it) {
		if (lit_state(it->get_literals()[1]) != LitState::L_SAT)
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
	// 🔹 Step 1: Flip inequality if RHS is negative
	if (bigger) {
		rhs *= -1;  // Convert RHS to positive
		for (auto& term : terms) {
			term.first *= -1;  // Multiply coefficients by -1
		}
	}

	// 🔹 Step 2: Convert each term correctly
	pb_constraint.reset_terms();
	pb_constraint.reset_coefficients();
	pb_constraint.reset_literals();
	for (auto& term : terms) {
		int coeff = term.first;
		int var = term.second;

		if (coeff < 0) {
			// 🔥 Apply transformation: x_i = 1 - x̅_i
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

	// 🔹 Sort terms by coefficient value (highest first)
	std::vector<std::pair<int, int>> sorted_terms = constraint.get_terms();
	std::sort(sorted_terms.begin(), sorted_terms.end(), [](auto& a, auto& b) {
		return abs(a.first) > abs(b.first);
		});

	// 🔹 Add literals contributing to the conflict
	for (const auto& term : sorted_terms) {
		int coeff = term.first;
		Lit lit = term.second;
		int var = l2v(lit);

		if ((state_pb[var] == VarState::V_TRUE &&  !(Neg(lit))) ||
			(state_pb[var] == VarState::V_FALSE && (Neg(lit)))) {

			conflictConstraint.insert_term(1,var);
			accumulated_sum += coeff;
			rhs_c += 1;


			std::cout << "Adding x" << var << "\n";

			if (accumulated_sum > rhs) {
				break;
			}
		}
	}

	conflictConstraint.set_rhs(rhs_c - 1);

	std::cout << "Learned PB Conflict Constraint: ";
	for (const auto& term : conflictConstraint.get_terms()) {
		std::cout << term.first << "x" << term.second << " ";
	}
	std::cout << "<= " << conflictConstraint.get_rhs() << "\n";

	return conflictConstraint;
}



//Constraint Solver::resolvePB(Constraint c1, Constraint c2, Lit l) {
//	Constraint result;
//	int var = l2v(l);
//	int coeff_var_c1 = getCoefficient(c1.get_terms(), var);
//	int coeff_var_c2 = getCoefficient(c2.get_terms(), var);
//	int lcm_coeff = lcm(coeff_var_c1, coeff_var_c2);
//	vector<pair<int, int>> terms_c1 = c1.get_terms();
//	vector<pair<int, int>> terms_c2 = c2.get_terms();
//
//	for (auto& term : terms_c1) {
//		if (term.second != var)
//		{
//			int coeff = term.first;
//			term.first = lcm_coeff / coeff_var_c1 * coeff;
//			result.insert_term(term.first, term.second);
//		}
//	}
//
//	for (auto& term : terms_c2) {
//		if (term.second != variable)
//		{
//			int coeff = term.first;
//			term.first = lcm_coeff / coeff_var_c2 * coeff;
//			result.insert_term(term.first, term.second);
//		}
//	}
//
//
//	result.set_rhs (lcm_coeff / coeff_var_c1 * c1.get_rhs() + lcm_coeff / coeff_var_c2 * c2.get_rhs());
//	return result;
//}
//
//int Solver::lcm(int a, int b) {
//	return (a / gcd(a, b)) * b;  // Prevents overflow
//}
//
//int Solver::gcd(int a, int b) {
//	if (b == 0)
//		return a;
//	return gcd(b, a % b);  // Recursively call with (b, a % b)
//}
//
//
//Constraint& Solver::saturatePB(Constraint& pb_constraint) {
//	int gcd_all = 0;
//	int rhs = pb_constraint.get_rhs();
//	// Compute GCD of all coefficients including rhs
//	for (auto& term : pb_constraint.get_terms()) {
//		gcd_all = gcd(gcd_all, abs(term.first));
//	}
//	gcd_all = gcd(gcd_all, abs(pb_constraint.get_rhs()));
//
//	// If GCD > 1, divide all terms
//	if (gcd_all > 1) {
//		for (auto& term : pb_constraint.get_terms()) {
//			term.first /= gcd_all;  // Reduce coefficient
//		}
//		rhs /= gcd_all;  // Reduce RHS
//	}
//	pb_constraint.set_rhs(rhs);
//
//	return pb_constraint;
//}

//bool PBSolver::solvePBConstraints() {
//	// 🔹 Step 1: Sort variables by coefficient (descending)
//
//
//	std::cout << "The value of nvar is: " << nvars << std::endl;
//	num_assignments = 0;
//	dl_pb = 0;
//
//	std::cout << "The value of nlits is: " << 2 * nvars << std::endl;
//	state_pb.assign(nvars + 1, VarState::V_UNASSIGNED);
//	prev_state_pb.assign(nvars + 1, VarState::V_UNASSIGNED);  // Store previous state
//	dlevel_pb.assign(nvars + 1, -1);  // Reset decision levels
//	reason_pb.assign(nvars*2 + 1,-1);
//	while (num_assignments != nvars) {
//		int best_var = choose_best_variable();
//		std::cout << "the best var is " << best_var << "\n";
//		propagatePBConstraints(best_var, VarState::V_TRUE, false);
//
//
//	}
//
//		std::cout << "Solution found \n";
//		return true;  // ✅ Constraint satisfied
//	
//
//}



#pragma endregion solving


/******************  main ******************************/

int main(int argc, char** argv){
	begin_time = cpuTime();
	parse_options(argc, argv);
	
	std::ifstream file("Input.pb");
	if (!file) {
		std::cerr << "Error: Cannot open input.pb file!\n";
		return 1;
	}
	
	S.read_pb(file);
	file.close();
	S.solve();	

	return 0;
}

//int main() {
//	
//	PBSolver S;
//	int best_var;
//
//	std::ifstream file("Input.pb");
//	if (!file) {
//		std::cerr << "Error: Cannot open input.pb file!\n";
//		return 1;
//	}
//
//	S.read_pb(file);
//	file.close();
//
//	// Print where variable x1 appears
//	S.print_variable_count(1);
//	S.print_variable_count(2);
//	S.print_variable_count(3);
//	S.print_variable_count(4);
//
//	
//	S.solvePBConstraints();
//
//
//	return 0;
//
//}