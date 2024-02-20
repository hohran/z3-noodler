#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa/strings.hh>

#include "util.h"
#include "aut_assignment.h"
#include "length_decision_procedure.h"
#include <fstream>

#include "util/trace.h"

// test
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include <mata/nfa/builder.hh>


namespace smt::noodler {

    // TODO: this is nastyy
    BasicTerm begin_of(zstring of, zstring from) {
        return BasicTerm(BasicTermType::Variable, "BEGIN_OF_" + of.encode() + "_FROM_" + from.encode());
    }

    bool VarConstraint::check_side(const Concat& side) {
        return side.size() == 1 && side[0].get_name() == _name;
    }

    void VarConstraint::emplace(const Concat& c, std::map<zstring, zstring>& lit_conversion) {
        Concat n {};
        for (const BasicTerm& t : c) {
            if (BasicTermType::Literal == t.get_type()) {
                BasicTerm lit(BasicTermType::Literal, LengthDecisionProcedure::generate_lit_alias(t.get_name(), lit_conversion));
                n.emplace_back(lit);
            } else {
                n.emplace_back(t);
            }
        }

        _constr_eqs.emplace_back(n);
    }

    bool VarConstraint::add(const Predicate& pred, std::map<zstring, zstring>& lit_conversion) {
        if (check_side(pred.get_left_side())) {
            emplace(pred.get_right_side(), lit_conversion);
            return true;
        }
        if (check_side(pred.get_right_side())) {
            emplace(pred.get_left_side(), lit_conversion);
            return true;
        }

        // Fresh variable 
        emplace(pred.get_right_side(), lit_conversion);
        emplace(pred.get_left_side(), lit_conversion);

        return false;
    }

    const std::vector<zstring>& VarConstraint::get_lits() const {
        return _lits;
    }

    // LenNode align(const zstring& constr_var, const zstring& l1, const zstring& l2, std::map<zstring,zstring>& conv) {
    //     zstring l1_val = conv[l1];
    //     zstring l2_val = conv[l2];

        
    // }

    void VarConstraint::get_alignments(const std::vector<zstring>& side_lits) {
        for (const zstring& prev : this->_lits) {
            for (const zstring& n : side_lits) {
                std::cerr << "  psi(" << prev.encode() << ", " << n.encode() << ")\n";
            }
        }
    }

    void generate_begin_decl(const zstring& constr_var, const zstring& var, const BasicTerm& last, bool precise) {
        LenNode end_of_last = (last.get_type() == BasicTermType::Length)
            ? LenNode(0)
            : LenNode(LenFormulaType::PLUS, {begin_of(last.get_name(), constr_var), last});

        LenNode out = precise ? LenNode(LenFormulaType::EQ, {begin_of(var, constr_var), end_of_last})
            : LenNode(LenFormulaType::LEQ, {end_of_last, begin_of(var, constr_var)});
        
        std::cerr << out << std::endl;
    }

    void generate_begin_decl(const zstring& constr_var, const zstring& lit, const zstring& from) {
        LenNode out (LenFormulaType::EQ, {begin_of(lit, constr_var), LenNode(LenFormulaType::PLUS, {begin_of(lit, from), begin_of(from, constr_var)})});
        std::cerr << out << std::endl;
    }

    void generate_end_decl(const zstring& constr_var, const zstring& var, bool precise) {
        LenFormulaType ftype = precise ? LenFormulaType::EQ : LenFormulaType::LEQ;
        LenNode out (ftype, {
            LenNode(LenFormulaType::PLUS, {begin_of(var, constr_var), BasicTerm(BasicTermType::Variable, var)}),
            BasicTerm(BasicTermType::Variable, constr_var)
        });
        std::cerr << out << std::endl;
    }

    bool VarConstraint::parse(std::map<zstring,VarConstraint>& pool, std::map<zstring,zstring>& conv) {
        if (is_parsed == l_true) {
            return true;	// Already parsed
        }

        if (is_parsed == l_undef) {
            return false;	// Cycle
        }

        is_parsed = l_undef;	// Currently in parsing

        // parse derived
        for (const Concat& side : _constr_eqs) {
            for (const BasicTerm& t : side) {
                if (t.get_type() == BasicTermType::Variable) {

                    // parse constrained variables
                    if (pool.count(t.get_name())) {
                        if (pool[t.get_name()].parse(pool, conv) == false) {
                            return false;	// There is a cycle
                        }
                    }
                }
            }
        }

        is_parsed = l_true;

        std::cerr << "Processing " << this->_name << ":\n==========\n\n";

        // lits alignment
        std::cerr << "Alignment of literals:\n-----\n";
        for (const Concat& side : _constr_eqs) {
            std::vector<zstring> lits_in_side {};
            for (const BasicTerm& t : side) {
                if (t.get_type() == BasicTermType::Literal) {
                    lits_in_side.emplace_back(t.get_name());
                } else 
                if (t.get_type() == BasicTermType::Variable) {

                    // If the var is constrained
                    if (pool.count(t.get_name())) {                        
                        for (const zstring& l : pool[t.get_name()].get_lits()) {
                            lits_in_side.emplace_back(l);
                        }
                    }
                }
            }

            get_alignments(lits_in_side);
            for (const zstring& z : lits_in_side) {
                _lits.emplace_back(z);
            }
        }
        std::cerr << "-----\n\n";

        // kontys constraints e.g. x = uvw -> |x| = |u|+|v|+|w|
        std::cerr << "kontys constraints:\n-----\n";
        for (const Concat& side : _constr_eqs) {
            bool unconstrained = true;    // there are unconstrained variables
            std::vector<LenNode> side_len {};

            for (const BasicTerm& t : side) {

                // unconstrained variable
                if (t.get_type() == BasicTermType::Variable && pool.count(t.get_name()) == 0) {
                    unconstrained = false;
                } else {
                    side_len.emplace_back(t);
                }
            }
            if (unconstrained) {}
            LenNode out = unconstrained 
                ? LenNode(LenFormulaType::EQ, {LenNode(BasicTerm(BasicTermType::Variable, this->_name)), LenNode(LenFormulaType::PLUS, side_len)})
                : LenNode(LenFormulaType::NOT, {LenNode(LenFormulaType::LT, {LenNode(BasicTerm(BasicTermType::Variable, this->_name)), LenNode(LenFormulaType::PLUS, side_len)})});
            std::cerr << out << std::endl;
        }
        std::cerr << "-----\n\n";

        // begin constraints
        std::cerr << "begin constraints:\n-----\n";
        for (const Concat& side : _constr_eqs) {
            BasicTerm last (BasicTermType::Length);
            bool precise = true;    // there is no immediately previous filler variable

            for (const BasicTerm& t : side) {
                if (t.get_type() == BasicTermType::Literal) {
                    generate_begin_decl(this->_name, t.get_name(), last, precise);
                    last = t;
                    precise = true;
                } else {
                    // Var is constrained
                    if (pool.count(t.get_name())) {
                        generate_begin_decl(this->_name, t.get_name(), last, precise);
                        for (const zstring& lit : pool[t.get_name()].get_lits()) {
                            generate_begin_decl(this->_name, lit, t.get_name());
                        }
                        last = t;
                        precise = true;
                    } else {
                        precise = false;
                    }
                }
            }

            bool is_relevant = (last.get_type() == BasicTermType::Literal);
            is_relevant |= (last.get_type() == BasicTermType::Variable && pool.count(last.get_name()));

            if (is_relevant) {
                generate_end_decl(this->_name, last.get_name(), precise);
            }
        }
        std::cerr << "-----\n\n";

        std::cerr << "=========\n\n";
        return true;
    }

    std::string VarConstraint::to_string() const {
        std::string ret = "#####\n# VarConstraint: " + _name.encode() + "\n###\n#";
        bool first = true;
        for (const Concat& side : _constr_eqs) {
            if (!first) {
                ret += " =";
            }
            first = false;

            for (const BasicTerm& term : side) {
                // Literals will be displayed just by their name, not by value
                ret += " " + term.to_string();
            }
        }

        ret += "\n###\n# lits:";

        for (const zstring& t :_lits) {
            // for explicit: ... lname ...
            ret += " " + t.encode(); // + ((t.parent_var == "") ? "" : ("("+t.parent_var.encode()+")"));
        }

        ret += "\n#####\n";
        return ret;
    }



    static std::ostream& operator<<(std::ostream& os, const VarConstraint& vc) {
        os << vc.to_string();
        return os;
    }

    zstring LengthDecisionProcedure::generate_lit_alias(const zstring& value, std::map<zstring, zstring>& lit_conversion) {
        zstring new_lit_name = util::mk_noodler_var_fresh("lit").get_name();
        lit_conversion[new_lit_name] = value;
        return new_lit_name;
    }

    void LengthDecisionProcedure::add_to_pool(std::map<zstring, VarConstraint>& pool, const Predicate& pred) {
        bool in_pool = false;

        for (const Concat& side : pred.get_params()) {
            if (side.size() == 1 && side[0].get_type() == BasicTermType::Variable) {
                zstring var_name = side[0].get_name();
                if (pool.count(var_name) == 0) {
                    pool[var_name] = VarConstraint(var_name);
                }
                pool[var_name].add(pred, lit_conversion);

                in_pool = true;
            }
        }

        if (!in_pool) {
            zstring fresh = util::mk_noodler_var_fresh("f").get_name();
            pool[fresh] = VarConstraint(fresh);
        }
    }


    ///////////////////////////////////

    lbool LengthDecisionProcedure::compute_next_solution() {
        std::cerr << "len: compute_next_solution\n===========\n";
        for (const Predicate& pred : this->formula.get_predicates()) {
            std::cerr << pred << std::endl;
        }

        // Check for suitability
        std::vector<zstring> concat_vars = {};	// variables that have appeared in concatenation 
        
        for (const Predicate& pred : this->formula.get_predicates()) {
            if (pred.get_type() == PredicateType::NotContains) {
                // TODO: try to resolve not contains
                std::cerr << "len: Cant solve not contains.\n";
                return l_undef;
            }

            for (const Concat& side : pred.get_params()) {
                bool is_concat = side.size() > 1;

                for (const BasicTerm& var : side) {
                    // accept literals
                    if (init_aut_ass.is_singleton(var)) {
                        continue;
                    }

                    // Variable is not literal
                    if(init_aut_ass.at(var)->num_of_states() <= 1 || init_aut_ass.is_co_finite(var)) {
                        assert(var.get_type() == BasicTermType::Variable);
                        if (is_concat) {
                            zstring var_name = var.get_name();  // Name of the variable

                            // Check if variable was in any concatenation
                            for (zstring n : concat_vars) {
                                if (n == var_name) {
                                    return l_undef;
                                }
                            }
                            
                            // Note it as a concatenation variable
                            concat_vars.emplace_back(var_name);
                        }
                        continue;
                    }

                    std::cerr << "len: Not suitable.\n";
                    return l_undef;
                }
            }
        }
        // End check for suitability

        std::map<zstring, VarConstraint> pool{};

        for (const Predicate& pred : this->formula.get_predicates()) {
            add_to_pool(pool, pred);
        }        

        for (std::pair<zstring, VarConstraint> it : pool) {
            if (pool[it.first].parse(pool, lit_conversion) == false) {
                // There is a cycle
                return l_undef;	// We cannot solve this formula
            }
        }

        for (std::pair<zstring, VarConstraint> it : pool) {
            std::cerr << it.second << std::endl;
        }

        std::cerr << "\n\nConversions:\n+--------\n";
        for (const std::pair<const zstring, zstring>& conv : lit_conversion) {
            std::cerr << "| " + conv.first.encode() + " : \"" + conv.second.encode() << "\"\n";
        }

        return l_undef;
    }

    std::pair<LenNode, LenNodePrecision> LengthDecisionProcedure::get_lengths() {
        // TODO if we choose to support multiconcatenations, we will need to add underapprox flag
        LenNodePrecision precision = LenNodePrecision::PRECISE;
        LenNode len_formula = LenNode(LenFormulaType::AND, {this->computed_len_formula, this->preprocessing_len_formula, LenNode(LenFormulaType::AND, this->implicit_len_formula)});

        return {len_formula, precision};    
    }

    void LengthDecisionProcedure::init_computation() {
        std::cout << "here.\n";
        STRACE("str", tout << "len: Initializing computation..." << std::endl);
    }

    lbool LengthDecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {
        
        FormulaPreprocessor prep_handler(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

        STRACE("str", tout << "len: Preprocessing..." << std::endl);

        // std::ofstream out("len_dec_proc.txt");

        // out << "preprocess\n===========\n";
        // out << "Predicates:\n";
        // for (const Predicate& p : this->formula.get_predicates()) {
        //     out << p << '\n';
        // }

        // out << "\npreprocessing...\n\n";

        prep_handler.reduce_diseqalities();
        // out << "Reduce disequalities:\n-------\n";
        // for (const auto& p : prep_handler.get_formula().get_predicates()) {
        //     out << "  " << p.second << '\n';
        // }
        // out << "-------\n\n";

        prep_handler.underapprox_languages();

        prep_handler.propagate_eps();
        // out << "Propagate epsilon:\n-------\n";
        // for (const auto& p : prep_handler.get_formula().get_predicates()) {
        //     out << "  " << p.second << '\n';
        // }
        // out << "-------\n\n";

        prep_handler.propagate_variables();
        // out << "Propagate variables:\n-------\n";
        // for (const auto& p : prep_handler.get_formula().get_predicates()) {
        //     out << "  " << p.second << '\n';
        // }
        // out << "-------\n\n";

        prep_handler.generate_identities();
        // out << "Generate identities:\n-------\n";
        // for (const auto& p : prep_handler.get_formula().get_predicates()) {
        //     out << "  " << p.second << '\n';
        // }
        // out << "-------\n\n";

        prep_handler.propagate_variables();
        // out << "Propagate variables:\n-------\n";
        // for (const auto& p : prep_handler.get_formula().get_predicates()) {
        //     out << "  " << p.second << '\n';
        // }
        // out << "-------\n\n";


        // prep_handler = FormulaPreprocessor(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

        prep_handler.remove_trivial();
        

        // out.close();

        
        // Refresh the instance
        this->formula = prep_handler.get_modified_formula();
        this->init_aut_ass = prep_handler.get_aut_assignment();
        this->init_length_sensitive_vars = prep_handler.get_len_variables();
        this->preprocessing_len_formula = prep_handler.get_len_formula();

        if(this->formula.get_predicates().size() > 0) {
            this->init_aut_ass.reduce(); // reduce all automata in the automata assignment
        }

        if(prep_handler.contains_unsat_eqs_or_diseqs()) {
            return l_false;
        }

        if (!this->init_aut_ass.is_sat()) {
            // some automaton in the assignment is empty => we won't find solution
            return l_false;
        }
        
        if (this->formula.get_predicates().empty()) {
            // preprocessing solved all (dis)equations => we set the solution (for lengths check)
            // TODO ----v
            // this->solution = SolvingState(this->init_aut_ass, {}, {}, {}, this->init_length_sensitive_vars, {});
            return l_true;
        }

        
        
        return l_undef;
    }

    bool LengthDecisionProcedure::is_suitable(const Formula &form, const AutAssignment& init_aut_ass) {
        // std::vector<zstring> concat_vars = {};	// variables that have appeared in concatenation 
        for (const Predicate& pred : form.get_predicates()) {
            if (pred.get_type() == PredicateType::NotContains) {
                // TODO: try to resolve not contains
                std::cerr << "len: Cant solve not contains.\n";
                return l_undef;
            }

            for (const Concat& side : pred.get_params()) {
                bool is_concat = side.size() > 1;

                for (const BasicTerm& var : side) {
                    // accept literals
                    if (init_aut_ass.is_singleton(var)) {
                        continue;
                    }

                    // Variables are Sigma* or co-finite
                    if(init_aut_ass.at(var)->num_of_states() <= 1 || init_aut_ass.is_co_finite(var)) {
                        continue;
                    }

                    /* move this after preprocessing
                    // Variable is not literal
                    if(init_aut_ass.at(var)->num_of_states() <= 1 || init_aut_ass.is_co_finite(var, len)) {
                        if (is_concat) {
                            zstring var_name = var.get_name();  // Name of the variable

                            // Check if variable was in any concatenation
                            for (zstring n : concat_vars) {
                                if (n == var_name) {
                                    std::cerr << "Not suitable 1.\n";
                                    std::cerr << var_name << std::endl;
                                    std::cerr << "===========" << std::endl;
                                    return false;
                                }
                            }
                            
                            // Note it as a concatenation variable
                            concat_vars.emplace_back(var_name);
                        }
                        continue;
                    }
                    */

                    std::cerr << "len: Not suitable.\n";
                    return false;
                }
            }
        }
        std::cerr << "len: Suitable.\n";
        return true;
    }

}