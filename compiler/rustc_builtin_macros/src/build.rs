use rustc_ast::ptr::P;
use rustc_ast::{self as ast, AttrVec, BlockCheckMode, Expr, LocalKind, MatchKind, PatKind, UnOp};
use rustc_ast::{attr, token, util::literal};
use rustc_span::source_map::Spanned;
use rustc_span::symbol::{kw, sym, Ident, Symbol};
use rustc_span::{Span, DUMMY_SP};
use thin_vec::{thin_vec, ThinVec};

pub(crate) struct E;

// njn: remove `pub` everywhere
impl E {
    pub fn path(span: Span, strs: Vec<Ident>) -> ast::Path {
        E::path_all(span, false, strs, vec![])
    }
    pub fn path_ident(span: Span, id: Ident) -> ast::Path {
        E::path(span, vec![id])
    }
    pub fn path_global(span: Span, strs: Vec<Ident>) -> ast::Path {
        E::path_all(span, true, strs, vec![])
    }
    pub fn path_all(
        span: Span,
        global: bool,
        mut idents: Vec<Ident>,
        args: Vec<ast::GenericArg>,
    ) -> ast::Path {
        assert!(!idents.is_empty());
        let add_root = global && !idents[0].is_path_segment_keyword();
        let mut segments = ThinVec::with_capacity(idents.len() + add_root as usize);
        if add_root {
            segments.push(ast::PathSegment::path_root(span));
        }
        let last_ident = idents.pop().unwrap();
        segments.extend(
            idents.into_iter().map(|ident| ast::PathSegment::from_ident(ident.with_span_pos(span))),
        );
        let args = if !args.is_empty() {
            let args = args.into_iter().map(ast::AngleBracketedArg::Arg).collect();
            Some(ast::AngleBracketedArgs { args, span }.into())
        } else {
            None
        };
        segments.push(ast::PathSegment {
            ident: last_ident.with_span_pos(span),
            id: ast::DUMMY_NODE_ID,
            args,
        });
        ast::Path { span, segments, tokens: None }
    }

    pub fn macro_call(
        span: Span,
        path: ast::Path,
        delim: ast::token::Delimiter,
        tokens: ast::tokenstream::TokenStream,
    ) -> P<ast::MacCall> {
        P(ast::MacCall {
            path,
            args: P(ast::DelimArgs {
                dspan: ast::tokenstream::DelimSpan { open: span, close: span },
                delim,
                tokens,
            }),
        })
    }

    pub fn ty_mt(ty: P<ast::Ty>, mutbl: ast::Mutability) -> ast::MutTy {
        ast::MutTy { ty, mutbl }
    }

    pub fn ty(span: Span, kind: ast::TyKind) -> P<ast::Ty> {
        P(ast::Ty { id: ast::DUMMY_NODE_ID, span, kind, tokens: None })
    }

    pub fn ty_infer(span: Span) -> P<ast::Ty> {
        E::ty(span, ast::TyKind::Infer)
    }

    pub fn ty_path(path: ast::Path) -> P<ast::Ty> {
        E::ty(path.span, ast::TyKind::Path(None, path))
    }

    // Might need to take bounds as an argument in the future, if you ever want
    // to generate a bounded existential trait type.
    pub fn ty_ident(span: Span, ident: Ident) -> P<ast::Ty> {
        E::ty_path(E::path_ident(span, ident))
    }

    pub fn anon_const(span: Span, kind: ast::ExprKind) -> ast::AnonConst {
        ast::AnonConst {
            id: ast::DUMMY_NODE_ID,
            value: P(ast::Expr {
                id: ast::DUMMY_NODE_ID,
                kind,
                span,
                attrs: AttrVec::new(),
                tokens: None,
            }),
        }
    }

    pub fn const_ident(span: Span, ident: Ident) -> ast::AnonConst {
        E::anon_const(span, ast::ExprKind::Path(None, E::path_ident(span, ident)))
    }

    pub fn ty_ref(
        span: Span,
        ty: P<ast::Ty>,
        lifetime: Option<ast::Lifetime>,
        mutbl: ast::Mutability,
    ) -> P<ast::Ty> {
        E::ty(span, ast::TyKind::Ref(lifetime, E::ty_mt(ty, mutbl)))
    }

    pub fn ty_ptr(span: Span, ty: P<ast::Ty>, mutbl: ast::Mutability) -> P<ast::Ty> {
        E::ty(span, ast::TyKind::Ptr(E::ty_mt(ty, mutbl)))
    }

    pub fn typaram(
        span: Span,
        ident: Ident,
        bounds: ast::GenericBounds,
        default: Option<P<ast::Ty>>,
    ) -> ast::GenericParam {
        ast::GenericParam {
            ident: ident.with_span_pos(span),
            id: ast::DUMMY_NODE_ID,
            attrs: AttrVec::new(),
            bounds,
            kind: ast::GenericParamKind::Type { default },
            is_placeholder: false,
            colon_span: None,
        }
    }

    pub fn trait_ref(path: ast::Path) -> ast::TraitRef {
        ast::TraitRef { path, ref_id: ast::DUMMY_NODE_ID }
    }

    pub fn poly_trait_ref(span: Span, path: ast::Path) -> ast::PolyTraitRef {
        ast::PolyTraitRef {
            bound_generic_params: ThinVec::new(),
            trait_ref: E::trait_ref(path),
            span,
        }
    }

    pub fn trait_bound(path: ast::Path, is_const: bool) -> ast::GenericBound {
        ast::GenericBound::Trait(
            E::poly_trait_ref(path.span, path),
            ast::TraitBoundModifiers {
                polarity: ast::BoundPolarity::Positive,
                constness: if is_const {
                    ast::BoundConstness::Maybe(DUMMY_SP)
                } else {
                    ast::BoundConstness::Never
                },
                asyncness: ast::BoundAsyncness::Normal,
            },
        )
    }

    pub fn lifetime(span: Span, ident: Ident) -> ast::Lifetime {
        ast::Lifetime { id: ast::DUMMY_NODE_ID, ident: ident.with_span_pos(span) }
    }

    pub fn lifetime_static(span: Span) -> ast::Lifetime {
        E::lifetime(span, Ident::new(kw::StaticLifetime, span))
    }

    pub fn stmt_expr(expr: P<ast::Expr>) -> ast::Stmt {
        ast::Stmt { id: ast::DUMMY_NODE_ID, span: expr.span, kind: ast::StmtKind::Expr(expr) }
    }

    pub fn stmt_let(sp: Span, mutbl: bool, ident: Ident, ex: P<ast::Expr>) -> ast::Stmt {
        E::stmt_let_ty(sp, mutbl, ident, None, ex)
    }

    pub fn stmt_let_ty(
        sp: Span,
        mutbl: bool,
        ident: Ident,
        ty: Option<P<ast::Ty>>,
        ex: P<ast::Expr>,
    ) -> ast::Stmt {
        let pat = if mutbl {
            E::pat_ident_binding_mode(sp, ident, ast::BindingMode::MUT)
        } else {
            E::pat_ident(sp, ident)
        };
        let local = P(ast::Local {
            pat,
            ty,
            id: ast::DUMMY_NODE_ID,
            kind: LocalKind::Init(ex),
            span: sp,
            colon_sp: None,
            attrs: AttrVec::new(),
            tokens: None,
        });
        E::stmt_local(local, sp)
    }

    /// Generates `let _: Type;`, which is usually used for type assertions.
    pub fn stmt_let_type_only(span: Span, ty: P<ast::Ty>) -> ast::Stmt {
        let local = P(ast::Local {
            pat: E::pat_wild(span),
            ty: Some(ty),
            id: ast::DUMMY_NODE_ID,
            kind: LocalKind::Decl,
            span,
            colon_sp: None,
            attrs: AttrVec::new(),
            tokens: None,
        });
        E::stmt_local(local, span)
    }

    pub fn stmt_local(local: P<ast::Local>, span: Span) -> ast::Stmt {
        ast::Stmt { id: ast::DUMMY_NODE_ID, kind: ast::StmtKind::Let(local), span }
    }

    pub fn stmt_item(sp: Span, item: P<ast::Item>) -> ast::Stmt {
        ast::Stmt { id: ast::DUMMY_NODE_ID, kind: ast::StmtKind::Item(item), span: sp }
    }

    pub fn block_expr(expr: P<ast::Expr>) -> P<ast::Block> {
        E::block(
            expr.span,
            thin_vec![ast::Stmt {
                id: ast::DUMMY_NODE_ID,
                span: expr.span,
                kind: ast::StmtKind::Expr(expr),
            }],
        )
    }
    pub fn block(span: Span, stmts: ThinVec<ast::Stmt>) -> P<ast::Block> {
        P(ast::Block {
            stmts,
            id: ast::DUMMY_NODE_ID,
            rules: BlockCheckMode::Default,
            span,
            tokens: None,
            could_be_bare_literal: false,
        })
    }

    pub fn expr(span: Span, kind: ast::ExprKind) -> P<ast::Expr> {
        P(ast::Expr { id: ast::DUMMY_NODE_ID, kind, span, attrs: AttrVec::new(), tokens: None })
    }

    pub fn expr_path(path: ast::Path) -> P<ast::Expr> {
        E::expr(path.span, ast::ExprKind::Path(None, path))
    }

    pub fn expr_ident(span: Span, id: Ident) -> P<ast::Expr> {
        E::expr_path(E::path_ident(span, id))
    }
    pub fn expr_self(span: Span) -> P<ast::Expr> {
        E::expr_ident(span, Ident::with_dummy_span(kw::SelfLower))
    }

    pub fn expr_macro_call(span: Span, call: P<ast::MacCall>) -> P<ast::Expr> {
        E::expr(span, ast::ExprKind::MacCall(call))
    }

    pub fn expr_binary(
        sp: Span,
        op: ast::BinOpKind,
        lhs: P<ast::Expr>,
        rhs: P<ast::Expr>,
    ) -> P<ast::Expr> {
        E::expr(sp, ast::ExprKind::Binary(Spanned { node: op, span: sp }, lhs, rhs))
    }

    pub fn expr_deref(sp: Span, e: P<ast::Expr>) -> P<ast::Expr> {
        E::expr(sp, ast::ExprKind::Unary(UnOp::Deref, e))
    }

    pub fn expr_addr_of(sp: Span, e: P<ast::Expr>) -> P<ast::Expr> {
        E::expr(sp, ast::ExprKind::AddrOf(ast::BorrowKind::Ref, ast::Mutability::Not, e))
    }

    pub fn expr_paren(sp: Span, e: P<ast::Expr>) -> P<ast::Expr> {
        E::expr(sp, ast::ExprKind::Paren(e))
    }

    pub fn expr_call(
        span: Span,
        expr: P<ast::Expr>,
        args: ThinVec<P<ast::Expr>>,
    ) -> P<ast::Expr> {
        E::expr(span, ast::ExprKind::Call(expr, args))
    }
    pub fn expr_call_ident(
        span: Span,
        id: Ident,
        args: ThinVec<P<ast::Expr>>,
    ) -> P<ast::Expr> {
        E::expr(span, ast::ExprKind::Call(E::expr_ident(span, id), args))
    }
    pub fn expr_call_global(
        sp: Span,
        fn_path: Vec<Ident>,
        args: ThinVec<P<ast::Expr>>,
    ) -> P<ast::Expr> {
        let pathexpr = E::expr_path(E::path_global(sp, fn_path));
        E::expr_call(sp, pathexpr, args)
    }
    pub fn expr_block(b: P<ast::Block>) -> P<ast::Expr> {
        E::expr(b.span, ast::ExprKind::Block(b, None))
    }
    pub fn field_imm(span: Span, ident: Ident, e: P<ast::Expr>) -> ast::ExprField {
        ast::ExprField {
            ident: ident.with_span_pos(span),
            expr: e,
            span,
            is_shorthand: false,
            attrs: AttrVec::new(),
            id: ast::DUMMY_NODE_ID,
            is_placeholder: false,
        }
    }
    pub fn expr_struct(
        span: Span,
        path: ast::Path,
        fields: ThinVec<ast::ExprField>,
    ) -> P<ast::Expr> {
        E::expr(
            span,
            ast::ExprKind::Struct(P(ast::StructExpr {
                qself: None,
                path,
                fields,
                rest: ast::StructRest::None,
            })),
        )
    }
    pub fn expr_struct_ident(
        span: Span,
        id: Ident,
        fields: ThinVec<ast::ExprField>,
    ) -> P<ast::Expr> {
        E::expr_struct(span, E::path_ident(span, id), fields)
    }

    pub fn expr_usize(span: Span, n: usize) -> P<ast::Expr> {
        let suffix = Some(ast::UintTy::Usize.name());
        let lit = token::Lit::new(token::Integer, sym::integer(n), suffix);
        E::expr(span, ast::ExprKind::Lit(lit))
    }

    pub fn expr_u32(span: Span, n: u32) -> P<ast::Expr> {
        let suffix = Some(ast::UintTy::U32.name());
        let lit = token::Lit::new(token::Integer, sym::integer(n), suffix);
        E::expr(span, ast::ExprKind::Lit(lit))
    }

    pub fn expr_bool(span: Span, value: bool) -> P<ast::Expr> {
        let lit = token::Lit::new(token::Bool, if value { kw::True } else { kw::False }, None);
        E::expr(span, ast::ExprKind::Lit(lit))
    }

    pub fn expr_str(span: Span, s: Symbol) -> P<ast::Expr> {
        let lit = token::Lit::new(token::Str, literal::escape_string_symbol(s), None);
        E::expr(span, ast::ExprKind::Lit(lit))
    }

    pub fn expr_byte_str(span: Span, bytes: Vec<u8>) -> P<ast::Expr> {
        let lit = token::Lit::new(token::ByteStr, literal::escape_byte_str_symbol(&bytes), None);
        E::expr(span, ast::ExprKind::Lit(lit))
    }

    /// `[expr1, expr2, ...]`
    pub fn expr_array(sp: Span, exprs: ThinVec<P<ast::Expr>>) -> P<ast::Expr> {
        E::expr(sp, ast::ExprKind::Array(exprs))
    }

    /// `&[expr1, expr2, ...]`
    pub fn expr_array_ref(sp: Span, exprs: ThinVec<P<ast::Expr>>) -> P<ast::Expr> {
        E::expr_addr_of(sp, E::expr_array(sp, exprs))
    }

    pub fn expr_some(sp: Span, expr: P<ast::Expr>) -> P<ast::Expr> {
        let some = E::std_path(&[sym::option, sym::Option, sym::Some]);
        E::expr_call_global(sp, some, thin_vec![expr])
    }

    pub fn expr_none(sp: Span) -> P<ast::Expr> {
        let none = E::std_path(&[sym::option, sym::Option, sym::None]);
        E::expr_path(E::path_global(sp, none))
    }
    pub fn expr_tuple(sp: Span, exprs: ThinVec<P<ast::Expr>>) -> P<ast::Expr> {
        E::expr(sp, ast::ExprKind::Tup(exprs))
    }

    pub fn expr_unreachable(span: Span) -> P<ast::Expr> {
        E::expr_macro_call(
            span,
            E::macro_call(
                span,
                E::path_global(
                    span,
                    [sym::std, sym::unreachable].map(|s| Ident::new(s, span)).to_vec(),
                ),
                ast::token::Delimiter::Parenthesis,
                ast::tokenstream::TokenStream::default(),
            ),
        )
    }

    pub fn expr_ok(sp: Span, expr: P<ast::Expr>) -> P<ast::Expr> {
        let ok = E::std_path(&[sym::result, sym::Result, sym::Ok]);
        E::expr_call_global(sp, ok, thin_vec![expr])
    }

    pub fn expr_try(sp: Span, head: P<ast::Expr>) -> P<ast::Expr> {
        let ok = E::std_path(&[sym::result, sym::Result, sym::Ok]);
        let ok_path = E::path_global(sp, ok);
        let err = E::std_path(&[sym::result, sym::Result, sym::Err]);
        let err_path = E::path_global(sp, err);

        let binding_variable = Ident::new(sym::__try_var, sp);
        let binding_pat = E::pat_ident(sp, binding_variable);
        let binding_expr = E::expr_ident(sp, binding_variable);

        // `Ok(__try_var)` pattern
        let ok_pat = E::pat_tuple_struct(sp, ok_path, thin_vec![binding_pat.clone()]);

        // `Err(__try_var)` (pattern and expression respectively)
        let err_pat = E::pat_tuple_struct(sp, err_path.clone(), thin_vec![binding_pat]);
        let err_inner_expr =
            E::expr_call(sp, E::expr_path(err_path), thin_vec![binding_expr.clone()]);
        // `return Err(__try_var)`
        let err_expr = E::expr(sp, ast::ExprKind::Ret(Some(err_inner_expr)));

        // `Ok(__try_var) => __try_var`
        let ok_arm = E::arm(sp, ok_pat, binding_expr);
        // `Err(__try_var) => return Err(__try_var)`
        let err_arm = E::arm(sp, err_pat, err_expr);

        // `match head { Ok() => ..., Err() => ... }`
        E::expr_match(sp, head, thin_vec![ok_arm, err_arm])
    }

    pub fn pat(span: Span, kind: PatKind) -> P<ast::Pat> {
        P(ast::Pat { id: ast::DUMMY_NODE_ID, kind, span, tokens: None })
    }
    pub fn pat_wild(span: Span) -> P<ast::Pat> {
        E::pat(span, PatKind::Wild)
    }
    pub fn pat_lit(span: Span, expr: P<ast::Expr>) -> P<ast::Pat> {
        E::pat(span, PatKind::Lit(expr))
    }
    pub fn pat_ident(span: Span, ident: Ident) -> P<ast::Pat> {
        E::pat_ident_binding_mode(span, ident, ast::BindingMode::NONE)
    }

    pub fn pat_ident_binding_mode(
        span: Span,
        ident: Ident,
        ann: ast::BindingMode,
    ) -> P<ast::Pat> {
        let pat = PatKind::Ident(ann, ident.with_span_pos(span), None);
        E::pat(span, pat)
    }
    pub fn pat_path(span: Span, path: ast::Path) -> P<ast::Pat> {
        E::pat(span, PatKind::Path(None, path))
    }
    pub fn pat_tuple_struct(
        span: Span,
        path: ast::Path,
        subpats: ThinVec<P<ast::Pat>>,
    ) -> P<ast::Pat> {
        E::pat(span, PatKind::TupleStruct(None, path, subpats))
    }
    pub fn pat_struct(
        span: Span,
        path: ast::Path,
        field_pats: ThinVec<ast::PatField>,
    ) -> P<ast::Pat> {
        E::pat(span, PatKind::Struct(None, path, field_pats, ast::PatFieldsRest::None))
    }
    pub fn pat_tuple(span: Span, pats: ThinVec<P<ast::Pat>>) -> P<ast::Pat> {
        E::pat(span, PatKind::Tuple(pats))
    }

    pub fn pat_some(span: Span, pat: P<ast::Pat>) -> P<ast::Pat> {
        let some = E::std_path(&[sym::option, sym::Option, sym::Some]);
        let path = E::path_global(span, some);
        E::pat_tuple_struct(span, path, thin_vec![pat])
    }

    pub fn arm(span: Span, pat: P<ast::Pat>, expr: P<ast::Expr>) -> ast::Arm {
        ast::Arm {
            attrs: AttrVec::new(),
            pat,
            guard: None,
            body: Some(expr),
            span,
            id: ast::DUMMY_NODE_ID,
            is_placeholder: false,
        }
    }

    pub fn arm_unreachable(span: Span) -> ast::Arm {
        E::arm(span, E::pat_wild(span), E::expr_unreachable(span))
    }

    pub fn expr_match(span: Span, arg: P<ast::Expr>, arms: ThinVec<ast::Arm>) -> P<Expr> {
        E::expr(span, ast::ExprKind::Match(arg, arms, MatchKind::Prefix))
    }

    pub fn expr_if(
        span: Span,
        cond: P<ast::Expr>,
        then: P<ast::Expr>,
        els: Option<P<ast::Expr>>,
    ) -> P<ast::Expr> {
        let els = els.map(|x| E::expr_block(E::block_expr(x)));
        E::expr(span, ast::ExprKind::If(cond, E::block_expr(then), els))
    }

    pub fn lambda(span: Span, ids: Vec<Ident>, body: P<ast::Expr>) -> P<ast::Expr> {
        let fn_decl = E::fn_decl(
            ids.iter().map(|id| E::param(span, *id, E::ty(span, ast::TyKind::Infer))).collect(),
            ast::FnRetTy::Default(span),
        );

        // FIXME -- We are using `span` as the span of the `|...|`
        // part of the lambda, but it probably (maybe?) corresponds to
        // the entire lambda body. Probably we should extend the API
        // here, but that's not entirely clear.
        E::expr(
            span,
            ast::ExprKind::Closure(Box::new(ast::Closure {
                binder: ast::ClosureBinder::NotPresent,
                capture_clause: ast::CaptureBy::Ref,
                constness: ast::Const::No,
                coroutine_kind: None,
                movability: ast::Movability::Movable,
                fn_decl,
                body,
                fn_decl_span: span,
                // FIXME(SarthakSingh31): This points to the start of the declaration block and
                // not the span of the argument block.
                fn_arg_span: span,
            })),
        )
    }

    pub fn lambda0(span: Span, body: P<ast::Expr>) -> P<ast::Expr> {
        E::lambda(span, Vec::new(), body)
    }

    pub fn lambda1(span: Span, body: P<ast::Expr>, ident: Ident) -> P<ast::Expr> {
        E::lambda(span, vec![ident], body)
    }

    pub fn lambda_stmts_1(
        span: Span,
        stmts: ThinVec<ast::Stmt>,
        ident: Ident,
    ) -> P<ast::Expr> {
        E::lambda1(span, E::expr_block(E::block(span, stmts)), ident)
    }

    pub fn param(span: Span, ident: Ident, ty: P<ast::Ty>) -> ast::Param {
        let arg_pat = E::pat_ident(span, ident);
        ast::Param {
            attrs: AttrVec::default(),
            id: ast::DUMMY_NODE_ID,
            pat: arg_pat,
            span,
            ty,
            is_placeholder: false,
        }
    }

    // `self` is unused but keep it as method for the convenience use.
    pub fn fn_decl(inputs: ThinVec<ast::Param>, output: ast::FnRetTy) -> P<ast::FnDecl> {
        P(ast::FnDecl { inputs, output })
    }

    pub fn item(
        span: Span,
        name: Ident,
        attrs: ast::AttrVec,
        kind: ast::ItemKind,
    ) -> P<ast::Item> {
        P(ast::Item {
            ident: name,
            attrs,
            id: ast::DUMMY_NODE_ID,
            kind,
            vis: ast::Visibility {
                span: span.shrink_to_lo(),
                kind: ast::VisibilityKind::Inherited,
                tokens: None,
            },
            span,
            tokens: None,
        })
    }

    pub fn item_static(
        span: Span,
        name: Ident,
        ty: P<ast::Ty>,
        mutability: ast::Mutability,
        expr: P<ast::Expr>,
    ) -> P<ast::Item> {
        E::item(
            span,
            name,
            AttrVec::new(),
            ast::ItemKind::Static(ast::StaticItem { ty, mutability, expr: Some(expr) }.into()),
        )
    }

    pub fn item_const(
        span: Span,
        name: Ident,
        ty: P<ast::Ty>,
        expr: P<ast::Expr>,
    ) -> P<ast::Item> {
        let defaultness = ast::Defaultness::Final;
        E::item(
            span,
            name,
            AttrVec::new(),
            ast::ItemKind::Const(
                ast::ConstItem {
                    defaultness,
                    // FIXME(generic_const_items): Pass the generics as a parameter.
                    generics: ast::Generics::default(),
                    ty,
                    expr: Some(expr),
                }
                .into(),
            ),
        )
    }

    // Builds `#[name]`.
    pub fn attr_word(name: Symbol, span: Span) -> ast::Attribute {
        let g = &E::sess.psess.attr_id_generator;
        attr::mk_attr_word(g, ast::AttrStyle::Outer, name, span)
    }

    // Builds `#[name = val]`.
    //
    // Note: `span` is used for both the identifier and the value.
    pub fn attr_name_value_str(name: Symbol, val: Symbol, span: Span) -> ast::Attribute {
        let g = &E::sess.psess.attr_id_generator;
        attr::mk_attr_name_value_str(g, ast::AttrStyle::Outer, name, val, span)
    }

    // Builds `#[outer(inner)]`.
    pub fn attr_nested_word(outer: Symbol, inner: Symbol, span: Span) -> ast::Attribute {
        let g = &E::sess.psess.attr_id_generator;
        attr::mk_attr_nested_word(g, ast::AttrStyle::Outer, outer, inner, span)
    }
}
