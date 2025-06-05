// Copyright (c) Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

use move_compiler_v2::external_checks::ExpChecker;
use move_model::{
    ast::{Exp, ExpData, Operation},
    model::FunctionEnv,
};

#[derive(Default)]
pub struct EqualOperandsInPureBinOp;

impl ExpChecker for EqualOperandsInPureBinOp {
    fn get_name(&self) -> String {
        "equal_operands_in_pure_bin_op".to_string()
    }

    fn visit_expr_pre(&mut self, env: &FunctionEnv, expr: &ExpData) {
        if let ExpData::Call(nid, op, params) = expr {
            if !(params.len() == 2 && expr_are_equal(&params[0], &params[1])) {
                return;
            }

            let Some(msg) = pure_bin_op_result(op, params, env) else {
                return;
            };

            let env = env.env();

            self.report(env, &env.get_node_loc(*nid), msg.as_str())
        }
    }
}

fn expr_are_equal(expr1: &ExpData, expr2: &ExpData) -> bool {
    use ExpData::*;
    match (expr1, expr2) {
        (LocalVar(_, s1), LocalVar(_, s2)) => s1 == s2,
        (Value(_, v1), Value(_, v2)) => v1 == v2,
        (Temporary(_, t1), Temporary(_, t2)) => t1 == t2,
        (Call(_, op1, args1), Call(_, op2, args2)) => {
            op1 == op2
                && args1.len() == args2.len()
                && args1
                    .iter()
                    .zip(args2.iter())
                    .all(|(a1, a2)| expr_are_equal(a1, a2))
        },
        _ => false,
    }
}

fn pure_bin_op_result(op: &Operation, exprs: &Vec<Exp>, env: &FunctionEnv) -> Option<String> {
    use Operation::*;

    let expr_display: String;

    let res = match op {
        Mod | Xor => "0",
        Le | Ge | Eq => "True",
        BitOr | BitAnd => {
            expr_display = exprs[0].display_for_fun(env).to_string();
            expr_display.as_str()
        },
        Div => "1",
        Neq | Lt | Gt => "False",
        // | And | Or // Already matched in another lint
        _ => return None,
    };

    Some(format!("This (pure) operation always returns {res}."))
}
