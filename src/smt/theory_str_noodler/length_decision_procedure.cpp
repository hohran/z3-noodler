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

    void VarConstraint::emplace(const Concat& c, std::map<zstring, BasicTerm>& lit_conversion) {
        Concat n {};
        for (const BasicTerm& t : c) {
            if (BasicTermType::Literal == t.get_type()) {
                BasicTerm lit(BasicTermType::Literal, LengthDecisionProcedure::generate_lit_alias(t, lit_conversion));
                n.emplace_back(lit);
            } else {
                n.emplace_back(t);
            }
        }

        _constr_eqs.emplace_back(n);
    }

    bool VarConstraint::add(const Predicate& pred, std::map<zstring, BasicTerm>& lit_conversion) {
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

    // TODO: rename
    LenNode VarConstraint::generate_kontys(const std::vector<LenNode>& side_len) {
        LenNode right = BasicTerm(BasicTermType::Variable, this->_name);
        // if there is no variable: length is 0, for one variable the length of the left side is its length, for more the length is their sum
        LenNode left = (side_len.size() == 0) ? LenNode(0)
            : ((side_len.size() == 1) ? LenNode(side_len[0]) : LenNode(LenFormulaType::PLUS, side_len));
        return LenNode(LenFormulaType::EQ, {right, left});
    }

    // LenNode align(const zstring& constr_var, const zstring& l1, const zstring& l2, std::map<zstring,zstring>& conv) {
    //     zstring l1_val = conv[l1];
    //     zstring l2_val = conv[l2];

        
    // }
    /**
     * @brief Compare first n characters of l1 with last n characters of l2 (e.g. l1=banana, l2=ababa, n=2 -> [ba]nana, aba[ba] -> true)
     * 
     * @return bool match of substrings
     */
    bool zstr_comp(const zstring& l1_val, const zstring& l2_val, unsigned n) {
        int s1 = 0;
        int s2 = l2_val.length() - n;

        if (s2 < 0) {
            s1 -= s2;
            n += s2;
            s2 = 0;
        }
        if (s1 + n > l1_val.length()) {
            n = l1_val.length() - s1;
        }

        for (unsigned i = 0; i < n; i++) {
            if (l1_val[s1+i] != l2_val[s2+i]) {
                return false;
            }
        }

        return true;
    }

    LenNode VarConstraint::align_terms_off(const BasicTerm& t1, const BasicTerm& t2, const std::map<zstring, BasicTerm>& conv) {
        LenNode t1_val = (t1.is_variable()) ? LenNode(t1) : LenNode(conv.at(t1.get_name()));
        LenNode t2_val = (t2.is_variable()) ? LenNode(t2) : LenNode(conv.at(t2.get_name()));

        return LenNode(LenFormulaType::OR, {
            LenNode(LenFormulaType::LEQ, {LenNode(LenFormulaType::PLUS, {begin_of(t1.get_name(), this->_name), t1_val}), begin_of(t2.get_name(), this->_name)}),
            LenNode(LenFormulaType::LEQ, {LenNode(LenFormulaType::PLUS, {begin_of(t2.get_name(), this->_name), t2_val}), begin_of(t1.get_name(), this->_name)})
        });
    }

    LenNode VarConstraint::align_literals(const zstring& l1, const zstring& l2, const std::map<zstring, BasicTerm>& conv) {
        zstring l1_val = conv.at(l1).get_name();
        zstring l2_val = conv.at(l2).get_name();

        if (l1_val.length() == 1) {
            if (l2_val.length() == 1) {
                if (l1_val[0] == l2_val[0]) {
                    return LenNode(LenFormulaType::TRUE, {});
                } else {
                    return LenNode(LenFormulaType::NOT, {LenNode(LenFormulaType::EQ, {begin_of(l1, this->_name), begin_of(l2, this->_name)})});
                }
            }
        }

        std::vector<unsigned> overlays{};

        for (unsigned n = 1; n <= l2_val.length() + l1_val.length() - 1; ++n) {
            if (zstr_comp(l1_val, l2_val, n)) {
                overlays.emplace_back(n);
            }
        }

        LenNode before (LenFormulaType::LEQ, {LenNode(LenFormulaType::PLUS, {begin_of(l1, this->_name), rational(l1_val.length())}), begin_of(l2, this->_name)});
        LenNode after (LenFormulaType::LEQ, {LenNode(LenFormulaType::PLUS, {begin_of(l2, this->_name), rational(l2_val.length())}), begin_of(l1, this->_name)});
        std::vector<LenNode> align{before, after};
        for (unsigned i : overlays) {
            // b(l1) = b(l2) + |l2| - i
            align.emplace_back(LenNode(LenFormulaType::EQ, {
                LenNode(LenFormulaType::PLUS, {begin_of(l1, this->_name), rational(i)}),
                LenNode(LenFormulaType::PLUS, {begin_of(l2, this->_name), rational(l2_val.length())})
            }));
        }

        return LenNode(LenFormulaType::OR, align);
    }

    // LenNode VarConstraint::get_lengths(const std::map<zstring,VarConstraint>& pool, const std::map<zstring,BasicTerm>& conv) {
    //     std::vector<LenNode> form{};

    //     // lits alignment
    //     for (const auto& a : _alignments) {
    //         form.emplace_back(align_literals(a.first, a.second, conv));
    //     }

    //     // kontys constraints e.g. x = uvw -> |x| = |u|+|v|+|w|
    //     // TODO: only generate restrictrions for length sensitive variables
    //     for (const Concat& side : _constr_eqs) {
    //         // bool unconstrained = true;    // there are unconstrained variables
    //         std::vector<LenNode> side_len {};

    //         for (const BasicTerm& t : side) {
    //             if (t.get_type() == BasicTermType::Literal) {
    //                 side_len.emplace_back(conv.at(t.get_name()));
    //             } else {
    //                 side_len.emplace_back(t);
    //             }
    //         }

    //         form.emplace_back(generate_kontys(side_len));
    //     }

    //     // begin constraints
    //     for (const Concat& side : _constr_eqs) {
    //         BasicTerm last (BasicTermType::Length);
    //         // bool precise = true;    // there is no immediately previous filler variable

    //         for (const BasicTerm& t : side) {
    //             form.emplace_back(generate_begin(t.get_name(), last));
    //             if (t.get_type() == BasicTermType::Variable && pool.count(t.get_name())) {
    //                 for (const zstring& lit : pool.at(t.get_name()).get_lits()) {
    //                     form.emplace_back(generate_begin(lit, t.get_name()));
    //                 }
    //             }
    //             last = t;
    //         }

    //         // if (last.get_type() != BasicTermType::Length) {
    //         //     // form.emplace_back(generate_end_var(last.get_name()));
    //         //     // Watch out for approximation
    //         // }

    //         // With even the filler variables
            
    //     }

    //     STRACE("str",
    //         tout << "Length constraints on variable " << this->_name << "\n-----\n";
    //         for (LenNode c : form) {
    //             tout << c << std::endl;
    //         }
    //         tout << "-----\n\n";
    //     );


    //     return LenNode(LenFormulaType::AND, form);
    // }

    LenNode VarConstraint::align_terms(const BasicTerm& t1, const BasicTerm& t2, const std::map<zstring, BasicTerm>& conv) {
        if (t1.is_variable() || t2.is_variable()) {
            return align_terms_off(t1, t2, conv);
        } else {
            return align_literals(t1.get_name(), t2.get_name(), conv);
        }
    }

    LenNode VarConstraint::get_lengths(const std::map<zstring,VarConstraint>& pool, const std::map<zstring,BasicTerm>& conv) {
        std::vector<LenNode> form{};

        // lits alignment
        for (const auto& a : _alignments) {
            // form.emplace_back(align_literals(a.first, a.second, conv));
            form.emplace_back(align_terms(a.first, a.second, conv));
        }

        // kontys constraints e.g. x = uvw -> |x| = |u|+|v|+|w|
        // TODO: only generate restrictrions for length sensitive variables
        for (const Concat& side : _constr_eqs) {
            // bool unconstrained = true;    // there are unconstrained variables
            std::vector<LenNode> side_len {};

            for (const BasicTerm& t : side) {
                if (t.get_type() == BasicTermType::Literal) {
                    side_len.emplace_back(conv.at(t.get_name()));
                } else {
                    side_len.emplace_back(t);
                }
            }

            form.emplace_back(generate_kontys(side_len));
        }

        // begin constraints
        for (const Concat& side : _constr_eqs) {
            BasicTerm last (BasicTermType::Length);
            // bool precise = true;    // there is no immediately previous filler variable

            for (const BasicTerm& t : side) {
                form.emplace_back(generate_begin(t.get_name(), last));
                if (t.get_type() == BasicTermType::Variable && pool.count(t.get_name())) {
                    // for (const zstring& lit : pool.at(t.get_name()).get_lits()) {
                    //     form.emplace_back(generate_begin(lit, t.get_name()));
                    // }
                    for (const BasicTerm& at : pool.at(t.get_name()).get_align_terms()) {
                        form.emplace_back(generate_begin(at.get_name(), t.get_name()));
                    }
                }
                last = t;
            }

            // if (last.get_type() != BasicTermType::Length) {
            //     // form.emplace_back(generate_end_var(last.get_name()));
            //     // Watch out for approximation
            // }

            // With even the filler variables
            
        }

        STRACE("str",
            tout << "Length constraints on variable " << this->_name << "\n-----\n";
            for (LenNode c : form) {
                tout << c << std::endl;
            }
            tout << "-----\n\n";
        );


        return LenNode(LenFormulaType::AND, form);
    }

    LenNode VarConstraint::generate_begin(const zstring& var_name, const BasicTerm& last, bool precise) {
        LenNode end_of_last = (last.get_type() == BasicTermType::Length)
            ? LenNode(0)
            : LenNode(LenFormulaType::PLUS, {begin_of(last.get_name(), this->_name), last});

        LenFormulaType ftype = precise ? LenFormulaType::EQ : LenFormulaType::LEQ;
        LenNode out = LenNode(ftype, {end_of_last, begin_of(var_name, this->_name)});
        
        return out;
    }

    LenNode VarConstraint::generate_begin(const zstring& lit, const zstring& from) {
        LenNode out (LenFormulaType::EQ, {begin_of(lit, this->_name), LenNode(LenFormulaType::PLUS, {begin_of(lit, from), begin_of(from, this->_name)})});
        return out;
    }

    LenNode VarConstraint::generate_end_var(const zstring& var_name, bool precise) {
        // TODO: check
        LenFormulaType ftype = precise ? LenFormulaType::EQ : LenFormulaType::LEQ;
        LenNode out (ftype, {
            LenNode(LenFormulaType::PLUS, {begin_of(var_name, this->_name), BasicTerm(BasicTermType::Variable, var_name)}),
            BasicTerm(BasicTermType::Variable, this->_name)
        });
        return out;
    }

    const std::vector<BasicTerm>& VarConstraint::get_align_terms() const {
        return this->_to_align;
    }

    bool VarConstraint::parse(std::map<zstring,VarConstraint>& pool, std::map<zstring,BasicTerm>& conv, const std::vector<BasicTerm>& multiconcat_vars) {
        if (is_parsed == l_true) {
            return true;	// Already parsed
        }

        if (is_parsed == l_undef) {
            return false;	// Cycle
        }

        is_parsed = l_undef;	// Currently in parsing

        for (const Concat& side : _constr_eqs) {
            // std::vector<zstring> lits_in_side {};
            std::vector<BasicTerm> to_align_in_side {};
            for (const BasicTerm& t : side) {
                if (t.get_type() == BasicTermType::Literal) {
                    to_align_in_side.emplace_back(t);
                }
                if (t.get_type() == BasicTermType::Variable) {
                    // parse constrained variables
                    if (pool.count(t.get_name())) {
                        if (pool[t.get_name()].parse(pool, conv, multiconcat_vars) == false) {
                            return false;	// There is a cycle
                        }
                        for (const BasicTerm& at : pool.at(t.get_name()).get_align_terms()) {
                            to_align_in_side.emplace_back(at);
                        }
                    }

                    if (std::find(multiconcat_vars.begin(), multiconcat_vars.end(), t) != multiconcat_vars.end()) {
                        to_align_in_side.emplace_back(t);
                    }
                }
            }

            // for (const zstring& l1 : _lits) {
            //     for (const zstring& l2 : lits_in_side) {
            //         _alignments.emplace_back(l1, l2);
            //     }
            // }
            for (const BasicTerm& at1 : _to_align) {
                for (const BasicTerm& at2 : to_align_in_side) {
                    _alignments.emplace_back(at1, at2);
                }
            }

            // for (const zstring& l : lits_in_side) {
            //     _lits.emplace_back(l);
            // }
            for (const BasicTerm& at : to_align_in_side) {
                _to_align.emplace_back(at);
            }
        }

        is_parsed = l_true;

        
        return true;
    }


    // bool VarConstraint::parse(std::map<zstring,VarConstraint>& pool, std::map<zstring,BasicTerm>& conv) {
    //     if (is_parsed == l_true) {
    //         return true;	// Already parsed
    //     }

    //     if (is_parsed == l_undef) {
    //         return false;	// Cycle
    //     }

    //     is_parsed = l_undef;	// Currently in parsing

    //     // parse derived
    //     for (const Concat& side : _constr_eqs) {
    //         std::vector<zstring> lits_in_side {};
    //         for (const BasicTerm& t : side) {
    //             if (t.get_type() == BasicTermType::Literal) {
    //                 lits_in_side.emplace_back(t.get_name());
    //             }
    //             if (t.get_type() == BasicTermType::Variable) {
    //                 // parse constrained variables
    //                 if (pool.count(t.get_name())) {
    //                     if (pool[t.get_name()].parse(pool, conv) == false) {
    //                         return false;	// There is a cycle
    //                     }

    //                     for (const zstring& lit : pool[t.get_name()].get_lits()) {
    //                         lits_in_side.emplace_back(lit);
    //                     }
    //                 }
    //             }
    //         }

    //         for (const zstring& l1 : _lits) {
    //             for (const zstring& l2 : lits_in_side) {
    //                 _alignments.emplace_back(l1, l2);
    //             }
    //         }

    //         for (const zstring& l : lits_in_side) {
    //             _lits.emplace_back(l);
    //         }
    //     }

    //     is_parsed = l_true;

        
    //     return true;
    // }

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

    zstring LengthDecisionProcedure::generate_lit_alias(const BasicTerm& lit, std::map<zstring, BasicTerm>& lit_conversion) {
        zstring new_lit_name = util::mk_noodler_var_fresh("lit").get_name();
        // lit_conversion[new_lit_name] = lit;
        lit_conversion.emplace(std::make_pair(new_lit_name, lit));
        return new_lit_name;
    }

    // void LengthDecisionProcedure::add_to_pool(std::map<zstring, VarConstraint>& pool, const Predicate& pred) {
    //     bool in_pool = false;

    //     for (const Concat& side : pred.get_params()) {
    //         if (side.size() == 1 && side[0].get_type() == BasicTermType::Variable) {
    //             zstring var_name = side[0].get_name();
    //             if (pool.count(var_name) == 0) {
    //                 pool[var_name] = VarConstraint(var_name);
    //             }
    //             pool[var_name].add(pred, lit_conversion);

    //             in_pool = true;
    //         }
    //     }

    //     if (!in_pool) {
    //         zstring fresh = util::mk_noodler_var_fresh("f").get_name();
    //         pool[fresh] = VarConstraint(fresh);
    //         pool[fresh].add(pred, lit_conversion);
    //     }
    // }
    
    void LengthDecisionProcedure::add_to_pool(std::map<zstring, VarConstraint>& pool, const Predicate& pred) {
        assert(pred.get_left_side().size() == 1 && pred.get_left_side()[0].is_variable());
        zstring constrvar_name = pred.get_left_side()[0].get_name();

        if (pool.count(constrvar_name) == 0) {
            pool[constrvar_name] = VarConstraint(constrvar_name);
        }
        pool[constrvar_name].emplace(pred.get_right_side(), lit_conversion);
    }


    ///////////////////////////////////

    /**
     * @brief Check if t1 is dependent on t2
     * 
     * @param t1 
     * @param t2 
     * @param dependency_graph ACYCLIC tree with all dependencies
     * @return true - t1 is dependent on t2
     */
    bool check_dependency_inner(const BasicTerm& t1, const BasicTerm& t2, const std::map<BasicTerm,BasicTerm>& dependency_graph) {
        if (t1 == t2) {
            return true;
        }

        BasicTerm child = t1;
        while (true) {
            if (dependency_graph.count(child) == 0) 
                break;
            
            BasicTerm parent = dependency_graph.at(child);
            if (parent == t2)
                return true;
            
            child = parent;         
        }
        return false;
    }

    /**
     * @brief Check if t1 and t2 are dependent
     * 
     * @param t1 basicterm to check
     * @param t2 basicterm to check
     * @param dependency_graph ACYCLIC tree with all dependencies
     * @return true - dependent
     */
    bool check_dependency(const BasicTerm& t1, const BasicTerm& t2, const std::map<BasicTerm,BasicTerm>& dependency_graph) {
        if (check_dependency_inner(t1, t2, dependency_graph))
            return true;
        if (check_dependency_inner(t2, t1, dependency_graph))
            return true;
        return false;
    }

    /**
     * @brief check if there are dependent terms in to_check
     * 
     * @param to_check vector of terms
     * @param dependency_graph ACYCLIC tree with all dependencies
     * @return true - dependent
     */
    bool check_dependencies(const std::vector<BasicTerm>& to_check, const std::map<BasicTerm,BasicTerm>& dependency_graph) {
        for (size_t i = 0; i < to_check.size(); i++) {
            for (size_t j = i+1; j < to_check.size(); j++) {
                if (check_dependency(to_check[i], to_check[j], dependency_graph))
                    return true;
            }
        }
        return false;
    }

    lbool LengthDecisionProcedure::compute_next_solution() {
        // TODO: add underapprox for multiconcat on vars from different parent vars

        STRACE("str", tout << "len: compute_compute_next_solution...\n"; );

        STRACE("str",
            tout << "formula after preprocess:\n";
            for (const Predicate& pred : this->formula.get_predicates()) {
                tout << pred << std::endl;
            }
            tout << std::endl;
        );

        // Check for suitability
        // std::vector<BasicTerm> concat_vars = {}; 
        std::map<BasicTerm,BasicTerm> conc = {};	// variables that have appeared in concatenation
        std::map<BasicTerm,std::vector<BasicTerm>> multiconc = {};	// variables that have appeared in concatenation more than once -> their constrained variables
        
        // // TODO: compact to a function
        // for (const Predicate& pred : this->formula.get_predicates()) {
        //     for (const Concat& side : pred.get_params()) {
        //         if (side.size() <= 1) {
        //             continue;
        //         }

        //         for (const BasicTerm& t : side) {
        //             if (t.is_literal()) {
        //                 continue;
        //             }

        //             if (std::find(concat_vars.begin(), concat_vars.end(), t) == concat_vars.end()) {
        //                 concat_vars.emplace_back(t);
        //                 continue;
        //             } else {
        //                 STRACE("str", tout << "multiconcat on " << t.to_string() << std::endl; );
        //                 return l_undef;
        //             }

        //             STRACE("str", tout << "term " << t << "is inappropriate for len dec proc\n"; );
        //             return l_undef;
        //         }
        //     }
        // }
        // // End check for suitability

        for (const Predicate& pred : this->formula.get_predicates()) {
            assert(pred.get_left_side().size() == 1 && pred.get_left_side()[0].is_variable());
            BasicTerm constrvar = pred.get_left_side()[0];

            for (const BasicTerm& t : pred.get_right_side()) {
                if (t.is_literal())
                    continue;
                
                if (conc.count(t) == 0) {
                    conc.insert({t,constrvar});
                    continue;
                }

                // t has already appeared in concatenation
                if (multiconc.count(t) == 0) {
                    multiconc.insert({t,{conc.at(t)}});    // create new map with the first cvar of t
                }
                multiconc[t].emplace_back(constrvar);
            }
        }

        std::vector<BasicTerm> multiconcat_vars = {};
        for (const std::pair<BasicTerm,std::vector<BasicTerm>>& it : multiconc) {
            if (check_dependencies(it.second, conc) == true) {
                STRACE("str", tout << "len: term " << it.first << " appears way too much.\n"; );
                return l_undef;
            }

            multiconcat_vars.emplace_back(it.first);
            this->precision = LenNodePrecision::UNDERAPPROX;
        }

        STRACE("str", tout << "Proceeding to computing length constraints.\n"; );

        std::map<zstring, VarConstraint> pool{};

        for (const Predicate& pred : this->formula.get_predicates()) {
            add_to_pool(pool, pred);
        }   

        STRACE("str",
            tout << "Conversions:\n-----\n";
            for (auto c : lit_conversion) {
                tout << c.first << " : " << c.second << std::endl;
            }
            tout << "-----\n";
        );  

        for (std::pair<zstring, VarConstraint> it : pool) {
            if (pool[it.first].parse(pool, lit_conversion, multiconcat_vars) == false) {
                // There is a cycle
                STRACE("str", tout << "len: Cyclic dependecy.\n";);
                return l_undef;	// We cannot solve this formula
            }
        }

        // Change if there is filler var filter
        for (const BasicTerm& v : this->formula.get_vars()) {
            implicit_len_formula.emplace_back(LenNode(LenFormulaType::LEQ, {0, v}));
        }

        for (std::pair<zstring, VarConstraint> it : pool) {
            computed_len_formula.emplace_back(pool[it.first].get_lengths(pool, lit_conversion));
        }

        STRACE("str", tout << "len: Finished computing.\n");
        return l_true;
    }

    std::pair<LenNode, LenNodePrecision> LengthDecisionProcedure::get_lengths() {
        // TODO if we choose to support multiconcatenations, we will need to add underapprox flag
        STRACE("str", tout << "len: get_lengths:\n"; );
        LenNode len_formula = LenNode(LenFormulaType::AND, {
            this->preprocessing_len_formula, 
            LenNode(LenFormulaType::AND, this->implicit_len_formula), 
            LenNode(LenFormulaType::AND, this->computed_len_formula)
        });

        for (const auto& t : init_aut_ass) {
            BasicTerm term = t.first;
            std::set<smt::noodler::BasicTerm> vars_in_eqs = this->formula.get_vars();    // Variables in all predicates

            // term does not appear in any predicate
            if (vars_in_eqs.find(term) == vars_in_eqs.end()) {
                len_formula.succ.emplace_back(this->init_aut_ass.get_lengths(term));
            }
        }

        return {len_formula, this->precision};    
    }

    void LengthDecisionProcedure::init_computation() {
        STRACE("str", tout << "len: Initializing computation..." << std::endl);
    }

    lbool LengthDecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {
        
        FormulaPreprocessor prep_handler(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

        STRACE("str", tout << "len: Preprocessing..." << std::endl);

        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities(); // only makes variable a literal or removes the disequation 

        // Underapproximate if it contains inequations
        for (const BasicTerm& t : this->formula.get_vars()) {
            if (prep_handler.get_aut_assignment().is_co_finite(t)) {
                prep_handler.underapprox_languages();
                this->precision = LenNodePrecision::UNDERAPPROX;
                STRACE("str", tout << "UNDERAPPROXIMATE languages\n";);
                break;
            }
        }

        prep_handler.propagate_eps();
        STRACE("str", tout << "Propagate epsilon\n";);

        prep_handler.propagate_variables();
        STRACE("str", tout << "Propagate variables\n";);

        prep_handler.generate_identities();
        STRACE("str", tout << "Generate identities:\n"; );

        prep_handler.propagate_variables();
        STRACE("str", tout << "Propagate variables\n";);

        prep_handler.remove_trivial();
        STRACE("str", tout << "Remove trivial\n";);

        prep_handler.replace_vars_with_lits();
        STRACE("str", tout << "Replace variables with literals\n";);
        prep_handler.my_separate_eqs();
        STRACE("str", tout << "My separate eqs\n";);

        
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

        return l_undef;
    }

    bool LengthDecisionProcedure::is_suitable(const Formula &form, const AutAssignment& init_aut_ass) {
        // std::vector<zstring> concat_vars = {};	// variables that have appeared in concatenation 
        STRACE("str", tout << "num of preds: " << form.get_predicates().size() << std::endl;);
        for (const Predicate& pred : form.get_predicates()) {
            if(!pred.is_eq_or_ineq()) {
                STRACE("str", tout << "Can only solve word (dis)equations.\n");
                return false;
            }
        }

        for (const BasicTerm& t : form.get_vars()) {
            // t has language of sigma*
            if(init_aut_ass.at(t)->num_of_states() <= 1) {
                    continue;
            }

            // t is co-finite (we can underapproximate it)
            if(init_aut_ass.is_co_finite(t)) {
                continue;
            }

            // t is a literal - get shortest words
            if(init_aut_ass.is_singleton(t)) {
                continue;
            }
            return false;
        }

        STRACE("str", tout << "Suitable.\n"; );
        return true;
    }

}