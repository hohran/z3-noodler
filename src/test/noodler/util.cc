#include <iostream>
#include <algorithm>
#include <utility>

#include <catch2/catch_test_macros.hpp>
#include <mata/parser/re2parser.hh>
#include <smt/theory_str_noodler/decision_procedure.h>
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "ast/reg_decl_plugins.h"
#include "test_utils.h"

using namespace smt::noodler;

TEST_CASE("theory_str_noodler::util") {
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params };
    theory_str_noodler_params str_params{};
    TheoryStrNoodlerCUT noodler{ctx, ast_m, str_params };
    std::set<uint32_t> alphabet{ '\x78', '\x79', '\x7A' };
    auto& m_util_s{ noodler.m_util_s };
    auto& m_util_a{ noodler.m_util_a };
    auto& m{ noodler.m };

    SECTION("util::get_dummy_symbols()") {
        vector<util::expr_pair> disequations{};
        auto expr_hex_char{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("x\x45")) };
        auto expr_hex_char2{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("y\x02")) };
        auto expr_hex_char3{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("z\x03")) };

        disequations.insert(std::make_pair(
                obj_ref<expr, ast_manager>{ expr_hex_char->get_arg(0), ast_m },
                obj_ref<expr, ast_manager>{ expr_hex_char->get_arg(0), ast_m }
        ));
        disequations.insert(std::make_pair(
                obj_ref<expr, ast_manager>{ expr_hex_char2->get_arg(0), ast_m },
                obj_ref<expr, ast_manager>{ expr_hex_char3->get_arg(0), ast_m }
        ));

        alphabet.insert({ '\x45', '\x02', '\x03', '\x00' });
        std::set<uint32_t> dummy_symbols{ util::get_dummy_symbols(disequations.size(), alphabet) };
        CHECK(dummy_symbols == std::set<uint32_t>{ '\x01', '\x04' });
        CHECK(alphabet == std::set<uint32_t>{ '\x00', '\x01', '\x02', '\x03', '\x04', '\x45', '\x78', '\x79', '\x7a' });
    }

    SECTION("util::get_symbols()") {
        vector<util::expr_pair> disequations{};
        auto expr_hex_char{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("x\x45")) };
        auto expr_hex_char2{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("wy\x02")) };
        auto expr_concat{ m_util_s.re.mk_concat(expr_hex_char, m_util_s.re.mk_star(expr_hex_char2)) };

        noodler.extract_symbols(expr_concat, alphabet);
        CHECK(alphabet == std::set<uint32_t>{ '\x02', '\x45', '\x77', '\x78', '\x79', '\x7a' });
    }

    SECTION("util::is_str_variable()") {
        expr_ref str_variable{ noodler.mk_str_var_fresh("var1"), m };
        CHECK(util::is_str_variable(str_variable, m_util_s));
        expr_ref str_literal{m_util_s.str.mk_string("var1"), m };
        CHECK(!util::is_str_variable(str_literal, m_util_s));
        expr_ref regex{ m_util_s.re.mk_to_re(m_util_s.str.mk_string(".*regex.*")), m };
        CHECK(!util::is_str_variable(regex, m_util_s));
        expr_ref int_literal{ m_util_a.mk_int(1), m };
        CHECK(!util::is_str_variable(int_literal, m_util_s));
    }

    SECTION("get_str_variables()") {
        obj_hashtable<expr> res;

        SECTION("String variables") {
            auto var1{ noodler.mk_str_var_fresh("var1") };
            auto var2{ noodler.mk_str_var_fresh("var2") };
            auto var3{ noodler.mk_str_var_fresh("var3") };
            auto concat1{ m_util_s.str.mk_concat(var1, var2) };
            auto concat2{ m_util_s.str.mk_concat(concat1, var3) };

            util::get_str_variables(concat2, m_util_s, m, res);
            CHECK(res.size() == 3);
            CHECK(res.contains(var1));
            CHECK(res.contains(var2));
            CHECK(res.contains(var3));
        }

        // FIXME: Uncomment and fix when we are able to detect all types of variables, int variables especially.
        //SECTION("Bool tree") {
        //    auto var1{ noodler.mk_int_var("var1") };
        //    auto var2{ noodler.mk_int_var("var2") };
        //    auto var3{ noodler.mk_int_var("var3") };

        //    auto expression{ expr_ref(m.mk_and(m.mk_and(m.mk_true(), m.mk_or(m.mk_false(), m.mk_eq(var1, var2))),
        //                      m.mk_or(m.mk_false(), m.mk_eq(var3, noodler.m_util_a.mk_int(1))) ), m) };

        //    util::get_str_variables(expression, m_util_s, m, res);
        //    CHECK(res.empty());
        //    util::get_int_variables(expression, m_util_s, m, res);
        //    for (auto tmp : res) {
        //        std::cout << mk_pp(tmp, m) << "\n";
        //    }
        //    CHECK(res.size() == 3);
        //    CHECK(res.contains(var1));
        //    CHECK(res.contains(var2));
        //    CHECK(res.contains(var3));
        //}

        SECTION("String constructs") {
            expr_ref var1{ noodler.mk_str_var_fresh("var1"), m };
            expr_ref var2{ noodler.mk_str_var_fresh("var2"), m };
            expr_ref var3{ noodler.mk_str_var_fresh("var3"), m };
            expr_ref re1{ noodler.m_util_s.re.mk_to_re(m_util_s.str.mk_string("re1")), m };
            expr_ref re2{ noodler.m_util_s.re.mk_to_re(m_util_s.str.mk_string("re2")), m };
            expr_ref re_eq{ m.mk_eq(re1, re2), m };
            expr_ref lit1{ m_util_s.str.mk_string("lit1"), m };
            expr_ref concat1{ m_util_s.str.mk_concat(var1, lit1), m };
            expr_ref concat2{ m_util_s.str.mk_concat(concat1, var2), m };
            expr_ref str_eq{ m.mk_eq(concat2, var3), m };
            expr_ref and_expr{ m.mk_and(re_eq, str_eq), m };

            util::get_str_variables(and_expr, m_util_s, m, res);
            CHECK(res.size() == 3);
            CHECK(res.contains(var1));
            CHECK(res.contains(var2));
            CHECK(res.contains(var3));
        }
    }

    SECTION("get_variable_names()") {
        std::unordered_set<std::string> res{};

        SECTION("String variables") {
            auto var1{ noodler.mk_str_var_fresh("var1") };
            auto var2{ noodler.mk_str_var_fresh("var2") };
            auto var3{ noodler.mk_str_var_fresh("var3") };
            auto lit1{ m_util_s.str.mk_string("lit1") };
            auto lit2{ m_util_s.str.mk_string("lit2") };
            auto concat1{ m_util_s.str.mk_concat(var1, lit1) };
            auto concat2{ m_util_s.str.mk_concat(concat1, var2) };
            auto concat3{ m_util_s.str.mk_concat(concat2, lit2) };
            auto concat4{ m_util_s.str.mk_concat(concat3, var3) };

            util::get_variable_names(concat4, m_util_s, m, res);
            CHECK(res == std::unordered_set<std::string>{ to_app(var1)->get_name().str(),
                                                           to_app(var2)->get_name().str(),
                                                           to_app(var3)->get_name().str() });
        }

        SECTION("String constructs") {
            expr_ref var1{ noodler.mk_str_var_fresh("var1"), m };
            expr_ref var2{ noodler.mk_str_var_fresh("var2"), m };
            expr_ref var3{ noodler.mk_str_var_fresh("var3"), m };
            expr_ref re1{ noodler.m_util_s.re.mk_to_re(m_util_s.str.mk_string("re1")), m };
            expr_ref re2{ noodler.m_util_s.re.mk_to_re(m_util_s.str.mk_string("re2")), m };
            expr_ref re_eq{ m.mk_eq(re1, re2), m };
            expr_ref lit1{ m_util_s.str.mk_string("lit1"), m };
            expr_ref concat1{ m_util_s.str.mk_concat(var1, lit1), m };
            expr_ref concat2{ m_util_s.str.mk_concat(concat1, var2), m };
            expr_ref str_eq{ m.mk_eq(concat2, var3), m };
            expr_ref and_expr{ m.mk_and(re_eq, str_eq), m };

            util::get_variable_names(and_expr, m_util_s, m, res);
            CHECK(res == std::unordered_set<std::string>{ to_app(var1)->get_name().str(),
                                                          to_app(var2)->get_name().str(),
                                                          to_app(var3)->get_name().str() });
        }
    }
}
