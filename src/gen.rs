use std::cell::RefCell;
use std::vec::Vec;
use std::rc::Rc;
use std::collections::HashMap;
use std::collections::hash_map::Entry;

use syntax::abi;
use syntax::ast;
use syntax::codemap::{Span, Spanned, respan, ExpnInfo, NameAndSpan, MacroBang};
use syntax::ext::base;
use syntax::ext::build::AstBuilder;
use syntax::ext::expand::ExpansionConfig;
use syntax::ext::quote::rt::ToTokens;
use syntax::feature_gate::Features;
use syntax::owned_slice::OwnedSlice;
use syntax::parse;
use syntax::parse::token::{InternedString, intern};
use syntax::attr::mk_attr_id;
use syntax::ptr::P;
use syntax::print::pprust::tts_to_string;

use super::LinkType;
use types::*;

struct GenCtx<'r> {
    ext_cx: base::ExtCtxt<'r>,
    unnamed_ty: usize,
    span: Span
}

fn first<A, B>((val, _): (A, B)) -> A {
    return val;
}

fn ref_eq<'a, 'b, T>(thing: &'a T, other: &'b T) -> bool {
    (thing as *const T) == (other as *const T)
}

fn empty_generics() -> ast::Generics {
    ast::Generics {
        lifetimes: Vec::new(),
        ty_params: OwnedSlice::empty(),
        where_clause: ast::WhereClause {
            id: ast::DUMMY_NODE_ID,
            predicates: Vec::new()
        }
    }
}

fn rust_id(ctx: &mut GenCtx, name: String) -> (String, bool) {
    let token = parse::token::Ident(ctx.ext_cx.ident_of(&name), parse::token::Plain);
    if token.is_any_keyword() || "bool" == &name {
        let mut s = "_".to_string();
        s.push_str(&name);
        (s, true)
    } else {
        (name, false)
    }
}

fn rust_type_id(ctx: &mut GenCtx, name: String) -> String {
    if "bool" == name ||
        "uint" == name ||
        "u8" == name ||
        "u16" == name ||
        "u32" == name ||
        "f32" == name ||
        "f64" == name ||
        "i8" == name ||
        "i16" == name ||
        "i32" == name ||
        "i64" == name ||
        "Self" == name ||
        "str" == name {
        let mut s = "_".to_string();
        s.push_str(&name);
        s
    } else {
        match name.as_str() {
            "int8_t" => "i8".to_string(),
            "uint8_t" => "u8".to_string(),
            "int16_t" => "i16".to_string(),
            "uint16_t" => "u16".to_string(),
            "int32_t" => "i32".to_string(),
            "uint32_t" => "u32".to_string(),
            "int64_t" => "i64".to_string(),
            "uint64_t" => "u64".to_string(),
            _ => {
                let (n, _) = rust_id(ctx, name);
                n
            }
        }
    }
}

fn unnamed_name(ctx: &mut GenCtx, name: String, filename: String) -> String {
    return if name.is_empty() {
        ctx.unnamed_ty += 1;
        format!("{}_unnamed_{}", filename, ctx.unnamed_ty)
    } else {
        name
    };
}

fn comp_name(kind: CompKind, name: &String) -> String {
    match kind {
        CompKind::Struct => struct_name(name),
        CompKind::Union  => union_name(name),
    }
}

fn struct_name(name: &String) -> String {
    format!("{}", name)
}

fn union_name(name: &String) -> String {
    format!("{}", name)
}

fn enum_name(name: &String) -> String {
    format!("{}", name)
}

fn gen_unmangle_method(ctx: &mut GenCtx,
                       v: &VarInfo,
                       counts: &mut HashMap<String, isize>,
                       explicit_self: ast::ExplicitSelf_)
                       -> P<ast::ImplItem> {
    let fndecl;
    let mut args = vec!();

    match explicit_self {
        ast::SelfStatic => (),
        ast::SelfRegion(_, mutable, _) => {
            let selfexpr = match mutable {
                ast::MutImmutable => quote_expr!(&ctx.ext_cx, &*self),
                ast::MutMutable => quote_expr!(&ctx.ext_cx, &mut *self),
            };
            args.push(selfexpr);
        },
        _ => unreachable!()
    }

    match v.ty {
        TFuncPtr(ref sig) => {
            fndecl = cfuncty_to_rs(ctx,
                                   &*sig.ret_ty, sig.args.as_slice(),
                                   false);
            let mut unnamed: usize = 0;
            let iter = if args.len() > 0 {
                sig.args[1..].iter()
            } else {
                sig.args.iter()
            };
            for arg in iter {
                let (ref n, _) = *arg;
                let argname = if n.is_empty() {
                    unnamed += 1;
                    format!("arg{}", unnamed)
                } else {
                    rust_id(ctx, n.clone()).0
                };
                let expr = ast::Expr {
                    id: ast::DUMMY_NODE_ID,
                    node: ast::ExprPath(None, ast::Path {
                        span: ctx.span,
                        global: false,
                        segments: vec!(ast::PathSegment {
                            identifier: ctx.ext_cx.ident_of(&argname),
                            parameters: ast::PathParameters::none()
                        })
                    }),
                    span: ctx.span,
                    attrs: None,
                };
                args.push(P(expr));
            }
        },
        _ => unreachable!()
    };

    let sig = ast::MethodSig {
        unsafety: ast::Unsafety::Unsafe,
        abi: abi::Rust,
        decl: P(fndecl),
        generics: empty_generics(),
        explicit_self: respan(ctx.span, explicit_self),
        constness: ast::Constness::NotConst,
    };

    let block = ast::Block {
        stmts: vec!(),
        expr: Some(P(ast::Expr {
            id: ast::DUMMY_NODE_ID,
            node: ast::ExprCall(
                P(ast::Expr {
                    id: ast::DUMMY_NODE_ID,
                    node: ast::ExprPath(None, ast::Path {
                        span: ctx.span,
                        global: false,
                        segments: vec!(ast::PathSegment {
                            identifier: ctx.ext_cx.ident_of(&v.mangled),
                            parameters: ast::PathParameters::none()
                        })
                    }),
                    span: ctx.span,
                    attrs: None,
                }),
                args
            ),
            span: ctx.span,
            attrs: None,
        })),
        id: ast::DUMMY_NODE_ID,
        rules: ast::DefaultBlock,
        span: ctx.span
    };

    let mut name = v.name.clone();
    let mut count = 0;
    match counts.get(&v.name) {
        Some(x) => {
            count = *x;
            name.push_str(&x.to_string());
        },
        None => ()
    }
    count += 1;
    counts.insert(v.name.clone(), count);

    let mut attrs = mk_doc_attr(ctx, v.comment.clone());
    attrs.push(respan(ctx.span, ast::Attribute_ {
        id: mk_attr_id(),
        style: ast::AttrStyle::Outer,
        value: P(respan(ctx.span, ast::MetaWord(InternedString::new("inline"))
        )),
        is_sugared_doc: false
    }));

    let item = ast::ImplItem {
        id: ast::DUMMY_NODE_ID,
        ident: ctx.ext_cx.ident_of(&name),
        vis: ast::Public,
        attrs: attrs,
        node: ast::ImplItemKind::Method(sig, P(block)),
        span: ctx.span
    };
    P(item)
}

pub fn gen_mod(links: &[(String, LinkType)], globs: Vec<Global>, span: Span) -> Vec<P<ast::Item>> {
    // Create a dummy ExtCtxt. We only need this for string interning and that uses TLS.
    let mut features = Features::new();
    features.allow_quote = true;
    let cfg = ExpansionConfig {
        crate_name: "xxx".to_string(),
        features: Some(&features),
        recursion_limit: 64,
        trace_mac: false,
    };
    let sess = &parse::ParseSess::new();
    let mut feature_gated_cfgs = vec![];
    let mut ctx = GenCtx {
        ext_cx: base::ExtCtxt::new(sess, Vec::new(), cfg, &mut feature_gated_cfgs),
        unnamed_ty: 0,
        span: span
    };
    ctx.ext_cx.bt_push(ExpnInfo {
        call_site: ctx.span,
        callee: NameAndSpan {
            format: MacroBang(intern("")),
            allow_internal_unstable: false,
            span: None
        }
    });
    let uniq_globs = tag_dup_decl(globs);

    let mut fs = vec!();
    let mut vs = vec!();
    let mut gs = vec!();
    for g in uniq_globs.into_iter() {
        match g {
            GOther => {}
            GFunc(_) => fs.push(g),
            GVar(_) => {
                let is_int_const = {
                    match g {
                        GVar(ref vi) => {
                            let v = vi.borrow();
                            v.is_const && v.val.is_some()
                        }
                        _ => unreachable!()
                    }
                };
                if is_int_const {
                    gs.push(g);
                } else {
                    vs.push(g);
                }
            }
            _ => gs.push(g)
        }
    }

    let mut defs = vec!();
    gs = remove_redundant_decl(gs);

    for g in gs.into_iter() {
        match g {
            GType(ti) => {
                let t = ti.borrow().clone();
                defs.extend(ctypedef_to_rs(&mut ctx, t.name.clone(), t.comment.clone(), &t.ty).into_iter())
            },
            GCompDecl(ci) => {
                {
                    let mut c = ci.borrow_mut();
                    c.name = unnamed_name(&mut ctx, c.name.clone(), c.filename.clone());
                }
                let c = ci.borrow().clone();
                defs.push(opaque_to_rs(&mut ctx, comp_name(c.kind, &c.name)));
            },
            GComp(ci) => {
                {
                    let mut c = ci.borrow_mut();
                    c.name = unnamed_name(&mut ctx, c.name.clone(), c.filename.clone());
                }
                let c = ci.borrow().clone();
                defs.extend(comp_to_rs(&mut ctx, comp_name(c.kind, &c.name),
                                       c).into_iter())
            },
            GEnumDecl(ei) => {
                {
                    let mut e = ei.borrow_mut();
                    e.name = unnamed_name(&mut ctx, e.name.clone(), e.filename.clone());
                }
                let e = ei.borrow().clone();
                defs.push(opaque_to_rs(&mut ctx, enum_name(&e.name)));
            },
            GEnum(ei) => {
                {
                    let mut e = ei.borrow_mut();
                    e.name = unnamed_name(&mut ctx, e.name.clone(), e.filename.clone());
                }
                let e = ei.borrow().clone();
                defs.extend(cenum_to_rs(&mut ctx, enum_name(&e.name), e.comment, e.items, e.layout).into_iter())
            },
            GVar(vi) => {
                let v = vi.borrow();
                let ty = cty_to_rs(&mut ctx, &v.ty, v.is_const);
                defs.push(const_to_rs(&mut ctx, v.name.clone(), v.val.unwrap(), ty));
            },
            _ => { }
        }
    }

    let vars = vs.into_iter().map(|v| {
        match v {
            GVar(vi) => {
                let v = vi.borrow();
                cvar_to_rs(&mut ctx, v.name.clone(), v.mangled.clone(), &v.ty, v.is_const)
            },
            _ => unreachable!()
        }
    }).collect();

    let mut unmangle_count: HashMap<String, isize> = HashMap::new();
    let funcs = {
        let func_list = fs.into_iter().map(|f| {
            match f {
                GFunc(vi) => {
                    let v = vi.borrow();
                    match v.ty {
                        TFuncPtr(ref sig) => {
                            let mut name = v.name.clone();
                            let mut count = 0;
                            match unmangle_count.get(&v.name) {
                                Some(x) => {
                                    count = *x;
                                    name.push_str(&x.to_string());
                                },
                                None => ()
                            }
                            count += 1;
                            unmangle_count.insert(v.name.clone(), count);

                            let decl = cfunc_to_rs(&mut ctx, name, v.mangled.clone(), v.comment.clone(),
                                                   &*sig.ret_ty, &sig.args[..],
                                                   sig.is_variadic, ast::Public);
                            (sig.abi, decl)
                        }
                        _ => unreachable!()
                    }
                },
                _ => unreachable!()
            }
        });

        let mut map: HashMap<abi::Abi, Vec<_>> = HashMap::new();
        for (abi, func) in func_list {
            match map.entry(abi) {
                Entry::Occupied(mut occ) => {
                    occ.get_mut().push(func);
                }
                Entry::Vacant(vac) => {
                    vac.insert(vec!(func));
                }
            }
        }
        map
    };

    if !Vec::is_empty(&vars) {
        defs.push(mk_extern(&mut ctx, links, vars, abi::C));
    }

    for (abi, funcs) in funcs.into_iter() {
        defs.push(mk_extern(&mut ctx, links, funcs, abi));
    }

    //let attrs = vec!(mk_attr_list(&mut ctx, "allow", ["dead_code", "non_camel_case_types", "uppercase_variables"]));

    defs
}

fn mk_extern(ctx: &mut GenCtx, links: &[(String, LinkType)],
             foreign_items: Vec<P<ast::ForeignItem>>,
             abi: abi::Abi) -> P<ast::Item> {
    let attrs = if links.is_empty() {
        Vec::new()
    } else {
        links.iter().map(|&(ref l, ref k)| {
            let k = match k {
                &LinkType::Default => None,
                &LinkType::Static => Some("static"),
                &LinkType::Framework => Some("framework")
            };
            let link_name = P(respan(ctx.span, ast::MetaNameValue(
                InternedString::new("name"),
                respan(ctx.span, ast::LitStr(intern(l).as_str(), ast::CookedStr))
            )));
            let link_args = match k {
                None => vec!(link_name),
                Some(ref k) => vec!(link_name, P(respan(ctx.span, ast::MetaNameValue(
                    InternedString::new("kind"),
                    respan(ctx.span, ast::LitStr(intern(k).as_str(), ast::CookedStr))
                ))))
            };
            respan(ctx.span, ast::Attribute_ {
                id: mk_attr_id(),
                style: ast::AttrStyle::Outer,
                value: P(respan(ctx.span, ast::MetaList(
                    InternedString::new("link"),
                    link_args)
                )),
                is_sugared_doc: false
            })
        }).collect()
    };

    let mut items = Vec::new();
    items.extend(foreign_items.into_iter());
    let ext = ast::ItemForeignMod(ast::ForeignMod {
        abi: abi,
        items: items
    });

    return P(ast::Item {
              ident: ctx.ext_cx.ident_of(""),
              attrs: attrs,
              id: ast::DUMMY_NODE_ID,
              node: ext,
              vis: ast::Inherited,
              span: ctx.span
           });
}

fn mk_impl(ctx: &mut GenCtx, ty: P<ast::Ty>,
           items: Vec<P<ast::ImplItem>>)
           -> P<ast::Item> {
    let ext = ast::ItemImpl(
        ast::Unsafety::Normal,
        ast::ImplPolarity::Positive,
        empty_generics(),
        None,
        ty,
        items
    );

    P(ast::Item {
        ident: ctx.ext_cx.ident_of(""),
        attrs: vec!(),
        id: ast::DUMMY_NODE_ID,
        node: ext,
        vis: ast::Inherited,
        span: ctx.span
    })
}

fn remove_redundant_decl(gs: Vec<Global>) -> Vec<Global> {
    fn check_decl(a: &Global, ty: &Type) -> bool {
        match *a {
          GComp(ref ci1) => match *ty {
              TComp(ref ci2) => {
                  ref_eq(ci1, ci2) && ci1.borrow().name.is_empty()
              },
              _ => false
          },
          GEnum(ref ei1) => match *ty {
              TEnum(ref ei2) => {
                  ref_eq(ei1, ei2) && ei1.borrow().name.is_empty()
              },
              _ => false
          },
          _ => false
        }
    }

    let typedefs: Vec<Type> = gs.iter().filter_map(|g|
        match *g {
            GType(ref ti) => Some(ti.borrow().ty.clone()),
            _ => None
        }
    ).collect();

    return gs.into_iter().filter(|g|
        !typedefs.iter().any(|t| check_decl(g, t))
    ).collect();
}

fn tag_dup_decl(gs: Vec<Global>) -> Vec<Global> {
    fn check(name1: &str, name2: &str) -> bool {
        !name1.is_empty() && name1 == name2
    }

    fn check_dup(g1: &Global, g2: &Global) -> bool {
        match (g1, g2) {
          (&GType(ref ti1), &GType(ref ti2)) => {
              let a = ti1.borrow();
              let b = ti2.borrow();
              check(&a.name, &b.name)
          },
          (&GComp(ref ci1), &GComp(ref ci2)) => {
              let a = ci1.borrow();
              let b = ci2.borrow();
              check(&a.name, &b.name)
          },
          (&GCompDecl(ref ci1), &GCompDecl(ref ci2)) => {
              let a = ci1.borrow();
              let b = ci2.borrow();
              check(&a.name, &b.name)
          },
          (&GEnum(ref ei1), &GEnum(ref ei2)) => {
              let a = ei1.borrow();
              let b = ei2.borrow();
              check(&a.name, &b.name)
          },
          (&GEnumDecl(ref ei1), &GEnumDecl(ref ei2)) => {
              let a = ei1.borrow();
              let b = ei2.borrow();
              check(&a.name, &b.name)
          },
          (&GVar(ref vi1), &GVar(ref vi2)) => {
              let a = vi1.borrow();
              let b = vi2.borrow();
              check(&a.name, &b.name) &&
              check(&a.mangled, &b.mangled)
          },
          (&GFunc(ref vi1), &GFunc(ref vi2)) => {
              let a = vi1.borrow();
              let b = vi2.borrow();
              check(&a.name, &b.name) &&
              check(&a.mangled, &b.mangled)
          },
          _ => false
        }
    }

    fn check_opaque_dup(g1: &Global, g2: &Global) -> bool {
        match (g1, g2) {
            (&GCompDecl(ref ci1), &GComp(ref ci2)) => {
                let a = ci1.borrow();
                let b = ci2.borrow();
                check(&a.name, &b.name)
            },
            (&GEnumDecl(ref ei1), &GEnum(ref ei2)) => {
                let a = ei1.borrow();
                let b = ei2.borrow();
                check(&a.name, &b.name)
            },
            _ => false,
        }
    }

    if gs.is_empty() {
        return gs;
    }

    let len = gs.len();
    let mut step: Vec<Global> = vec!();
    step.push(gs[0].clone());

    for i in 1..len {
        let mut dup = false;
        for j in 0..i {
            if i == j {
                continue;
            }
            if check_dup(&gs[i], &gs[j]) {
                dup = true;
                break;
            }
        }
        if !dup {
            step.push(gs[i].clone());
        }
    }

    let len = step.len();
    let mut res: Vec<Global> = vec!();
    for i in 0..len {
        let mut dup = false;
        match &step[i] {
            &GCompDecl(_) | &GEnumDecl(_) => {
                for j in 0..len {
                    if i == j {
                        continue;
                    }
                    if check_opaque_dup(&step[i], &step[j]) {
                        dup = true;
                        break;
                    }
                }
            },
            _ => (),
        }

        if !dup {
            res.push(step[i].clone());
        }
    }

    return res;
}

fn ctypedef_to_rs(ctx: &mut GenCtx, name: String, comment: String, ty: &Type) -> Vec<P<ast::Item>> {
    fn mk_item(ctx: &mut GenCtx, name: String, comment: String, ty: &Type) -> P<ast::Item> {
        let rust_name = rust_type_id(ctx, name);
        let rust_ty = if cty_is_translatable(ty) {
            cty_to_rs(ctx, ty, true)
        } else {
            cty_to_rs(ctx, &TVoid, true)
        };
        let base = ast::ItemTy(
            P(ast::Ty {
                id: ast::DUMMY_NODE_ID,
                node: rust_ty.node,
                span: ctx.span,
            }),
            empty_generics()
        );

        return P(ast::Item {
                  ident: ctx.ext_cx.ident_of(&rust_name),
                  attrs: mk_doc_attr(ctx, comment),
                  id: ast::DUMMY_NODE_ID,
                  node: base,
                  vis: ast::Public,
                  span: ctx.span
               });
    }

    return match *ty {
        TComp(ref ci) => {
            let is_empty = ci.borrow().name.is_empty();
            if is_empty {
                ci.borrow_mut().name = name.clone();
                let c = ci.borrow().clone();
                comp_to_rs(ctx, name, c)
            } else {
                vec!(mk_item(ctx, name, comment, ty))
            }
        },
        TEnum(ref ei) => {
            let is_empty = ei.borrow().name.is_empty();
            if is_empty {
                ei.borrow_mut().name = name.clone();
                let e = ei.borrow().clone();
                cenum_to_rs(ctx, name, e.comment, e.items, e.layout)
            } else {
                vec!(mk_item(ctx, name, comment, ty))
            }
        },
        _ => vec!(mk_item(ctx, name, comment, ty))
    }
}

fn comp_to_rs(ctx: &mut GenCtx, name: String, ci: CompInfo)
              -> Vec<P<ast::Item>> {
    match ci.kind {
        CompKind::Struct => cstruct_to_rs(ctx, name, ci),
        CompKind::Union =>  cunion_to_rs(ctx, name, ci.layout, ci.members),
    }
}

fn cstruct_to_rs(ctx: &mut GenCtx, name: String, ci: CompInfo) -> Vec<P<ast::Item>> {
    let layout = ci.layout;
    let members = &ci.members;
    let args = &ci.args;
    let methodlist = &ci.methods;
    let mut fields = vec!();
    let mut methods = vec!();
    // Nested composites may need to emit declarations and implementations as
    // they are encountered.  The declarations end up in 'extra' and are emitted
    // after the current struct.
    let mut extra = vec!();
    let mut unnamed: u32 = 0;
    let mut bitfields: u32 = 0;

    if ci.hide ||
       args.iter().any(|f| match *f { TVoid => true, _ => false }) {
        return vec!();
    }

    let id = rust_type_id(ctx, name.clone());
    let id_ty = P(mk_ty(ctx, false, vec!(id.clone())));

    if ci.has_vtable {
        let mut vffields = vec!();
        let base_vftable = if !members.is_empty() {
            if let CompMember::Field(ref fi) = members[0] {
                match fi.ty {
                    TComp(ref ci2) => {
                        let ci2 = ci2.borrow();
                        if ci2.has_vtable {
                            Some(format!("_vftable_{}", ci2.name))
                        } else {
                            None
                        }
                    },
                    _ => None
                }
            } else {
                None
            }
        } else {
            None
        };

        if let Some(ref base) = base_vftable {
            let field = ast::StructField_ {
                kind: ast::NamedField(ctx.ext_cx.ident_of("_base"), ast::Public),
                id: ast::DUMMY_NODE_ID,
                ty: P(mk_ty_args(ctx, false, vec!(base.clone()), vec!())),
                attrs: vec!(),
            };
            vffields.push(respan(ctx.span, field));
        }

        for vm in ci.vmethods.iter() {
            let ty = match vm.ty {
                TFuncPtr(ref sig) => {
                    let decl = cfuncty_to_rs(ctx, &*sig.ret_ty, sig.args.as_slice(), sig.is_variadic);
                    mk_fn_proto_ty(ctx, &decl, sig.abi)
                },
                _ => unreachable!()
            };
            let field = ast::StructField_ {
                kind: ast::NamedField(ctx.ext_cx.ident_of(&vm.name), ast::Public),
                id: ast::DUMMY_NODE_ID,
                ty: P(ty),
                attrs: vec!(),
            };
            vffields.push(respan(ctx.span, field));
        }

        let vf_name = format!("_vftable_{}", name);
        let item = ast::Item {
            ident: ctx.ext_cx.ident_of(&vf_name),
            attrs: vec!(mk_repr_attr(ctx, layout)),
            id: ast::DUMMY_NODE_ID,
            node: ast::ItemStruct(
                ast::VariantData::Struct(vffields, ast::DUMMY_NODE_ID),
                empty_generics()
            ),
            vis: ast::Public,
            span: ctx.span,
        };
        extra.push(P(item));

        if base_vftable == None {
            let vf_type = mk_ty_args(ctx, false, vec!(vf_name), vec!());
            fields.push(respan(ctx.span, ast::StructField_ {
                kind: ast::NamedField(ctx.ext_cx.ident_of("_vftable"), ast::Public),
                id: ast::DUMMY_NODE_ID,
                ty: P(mk_ptrty(ctx, &vf_type, true)),
                attrs: Vec::new()
            }));
        }
    }

    if members.is_empty() {
        let mut phantom_count = 0;
        for arg in args {
            let f_name = format!("_phantom{}", phantom_count);
            phantom_count += 1;
            let inner_type = P(cty_to_rs(ctx, &arg, true));
            fields.push(respan(ctx.span, ast::StructField_ {
                kind: ast::NamedField(
                    ctx.ext_cx.ident_of(&f_name),
                    ast::Public,
                ),
                id: ast::DUMMY_NODE_ID,
                ty: quote_ty!(&ctx.ext_cx, PhantomData<$inner_type>),
                attrs: vec!(),
            }));
        }
    }

    let mut anon_enum_count = 0;
    let mut setters = vec!();
    let mut has_destructor = ci.has_destructor;
    for m in members.iter() {
        if let &CompMember::Enum(ref ei) = m {
            let e = ei.borrow().clone();
            let ename = if e.name.is_empty() {
                let ename = format!("{}_enum{}", name, anon_enum_count);
                anon_enum_count += 1;
                ename
            } else {
                e.name.clone()
            };
            extra.extend(cenum_to_rs(ctx, ename, e.comment, e.items, e.layout).into_iter());
            continue;
        }

        fn comp_fields(m: &CompMember)
                       -> (Option<Rc<RefCell<CompInfo>>>, Option<FieldInfo>) {
            match m {
                &CompMember::Field(ref f) => { (None, Some(f.clone())) }
                &CompMember::Comp(ref rc_c) => {
                    let c = rc_c.borrow();
                    if c.members.len() == 1 {
                        comp_fields(&c.members[0])
                    } else {
                        (Some(rc_c.clone()), None)
                    }
                }
                &CompMember::CompField(ref rc_c, ref f) => { (Some(rc_c.clone()), Some(f.clone())) }
                _ => unreachable!()
            }
        }

        let (opt_rc_c, opt_f) = comp_fields(m);

        if let Some(f) = opt_f {
            if cty_has_destructor(&f.ty) {
                has_destructor = true;
            }
            if !cty_is_translatable(&f.ty) {
                continue;
            }
            let f_name = match f.bitfields {
                Some(_) => {
                    bitfields += 1;
                    format!("_bitfield_{}", bitfields)
                }
                None => rust_type_id(ctx, f.name.clone())
            };

            let mut offset: u32 = 0;
            if let Some(ref bitfields) = f.bitfields {
                for &(ref bf_name, bf_size) in bitfields.iter() {
                    setters.push(P(gen_bitfield_method(ctx, &f_name, bf_name, &f.ty, offset as usize, bf_size)));
                    offset += bf_size;
                }
                setters.push(P(gen_fullbitfield_method(ctx, &f_name, &f.ty, bitfields)))
            }

            let mut bypass = false;
            let f_ty = if let Some(ref rc_c) = opt_rc_c {
                if rc_c.borrow().members.len() == 1 {
                    if let CompMember::Field(ref inner_f) = rc_c.borrow().members[0] {
                        bypass = true;
                        inner_f.ty.clone()
                    } else {
                        f.ty.clone()
                    }
                } else {
                    f.ty.clone()
                }
            } else {
                f.ty.clone()
            };
            let f_ty = P(cty_to_rs(ctx, &f_ty, f.bitfields == None));

            fields.push(respan(ctx.span, ast::StructField_ {
                kind: ast::NamedField(
                    ctx.ext_cx.ident_of(&f_name),
                    ast::Public,
                ),
                id: ast::DUMMY_NODE_ID,
                ty: f_ty,
                attrs: mk_doc_attr(ctx, f.comment.clone())
            }));
            if bypass {
                continue;
            }
        }

        if let Some(rc_c) = opt_rc_c {
            let c = rc_c.borrow();
            if c.name.is_empty() {
                unnamed += 1;
                let field_name = format!("_bindgen_data_{}_", unnamed);
                fields.push(mk_blob_field(ctx, &field_name, c.layout));
                methods.extend(gen_comp_methods(ctx, &field_name, 0, c.kind, &c.members, &mut extra).into_iter());
            } else {
                extra.extend(comp_to_rs(ctx, comp_name(c.kind, &c.name), c.clone()).into_iter());
            }
        }
    }
    if !setters.is_empty() {
        extra.push(P(ast::Item {
            ident: ctx.ext_cx.ident_of(""),
            attrs: vec!(),
            id: ast::DUMMY_NODE_ID,
            node: ast::ItemImpl(
                ast::Unsafety::Normal,
                ast::ImplPolarity::Positive,
                empty_generics(),
                None,
                id_ty.clone(),
                setters
            ),
            vis: ast::Inherited,
            span: ctx.span
        }));
    }

    let variant_data = if fields.is_empty() {
        ast::VariantData::Unit(ast::DUMMY_NODE_ID)
    } else {
        ast::VariantData::Struct(fields, ast::DUMMY_NODE_ID)
    };
    let ty_params = args.iter().map(|gt| {
        let name = match gt {
            &TNamed(ref ti) => {
                ctx.ext_cx.ident_of(&ti.borrow().name)
            },
            _ => ctx.ext_cx.ident_of("")
        };
        ast::TyParam {
            ident: name,
            id: ast::DUMMY_NODE_ID,
            bounds: OwnedSlice::empty(),
            default: None,
            span: ctx.span
        }
    }).collect();

    let def = ast::ItemStruct(
        variant_data,
        ast::Generics {
            lifetimes: vec!(),
            ty_params: OwnedSlice::from_vec(ty_params),
            where_clause: ast::WhereClause {
                id: ast::DUMMY_NODE_ID,
                predicates: vec!()
            }
        }
    );

    let mut attrs = mk_doc_attr(ctx, ci.comment);
    attrs.push(mk_repr_attr(ctx, layout));
    if !has_destructor {
        attrs.push(mk_deriving_copy_attr(ctx));
    } else {
        attrs.push(mk_unsafe_no_drop_flag_attr(ctx));
    }
    let struct_def = P(ast::Item { ident: ctx.ext_cx.ident_of(&id),
        attrs: attrs,
        id: ast::DUMMY_NODE_ID,
        node: def,
        vis: ast::Public,
        span: ctx.span
    });

    let mut items = vec!(struct_def);
    if !methods.is_empty() {
        let impl_ = ast::ItemImpl(
            ast::Unsafety::Normal,
            ast::ImplPolarity::Positive,
            empty_generics(),
            None,
            id_ty.clone(),
            methods
        );
        items.push(
            P(ast::Item {
                ident: ctx.ext_cx.ident_of(&name),
                attrs: vec!(),
                id: ast::DUMMY_NODE_ID,
                node: impl_,
                vis: ast::Inherited,
                span: ctx.span}));
    }

    items.extend(extra.into_iter());

    let mut mangledlist = vec!();
    let mut unmangledlist = vec!();
    let mut unmangle_count: HashMap<String, isize> = HashMap::new();
    for v in methodlist {
        let v = v.clone();
        match v.ty {
            TFuncPtr(ref sig) => {
                let name = v.mangled.clone();
                let explicit_self = if v.is_static {
                    ast::SelfStatic
                } else if v.is_const {
                    ast::SelfRegion(None, ast::MutImmutable, ctx.ext_cx.ident_of("self"))
                } else {
                    ast::SelfRegion(None, ast::MutMutable, ctx.ext_cx.ident_of("self"))
                };
                unmangledlist.push(gen_unmangle_method(ctx, &v, &mut unmangle_count, explicit_self));
                mangledlist.push(cfunc_to_rs(ctx, name, String::new(), String::new(),
                                             &*sig.ret_ty, sig.args.as_slice(),
                                             sig.is_variadic, ast::Inherited));
            }
            _ => unreachable!()
        }
    }
    if mangledlist.len() > 0 {
        items.push(mk_extern(ctx, &vec!(), mangledlist, abi::C));
        items.push(mk_impl(ctx, id_ty, unmangledlist));
    }
    items
}

fn opaque_to_rs(ctx: &mut GenCtx, name: String) -> P<ast::Item> {
    let def = ast::ItemEnum(
        ast::EnumDef {
           variants: vec!()
        },
        empty_generics()
    );

    let id = rust_type_id(ctx, name);
    return P(ast::Item { ident: ctx.ext_cx.ident_of(&id),
              attrs: Vec::new(),
              id: ast::DUMMY_NODE_ID,
              node: def,
              vis: ast::Public,
              span: ctx.span
           });
}

fn cunion_to_rs(ctx: &mut GenCtx, name: String, layout: Layout, members: Vec<CompMember>) -> Vec<P<ast::Item>> {
    fn mk_item(ctx: &mut GenCtx, name: String, item: ast::Item_, vis:
               ast::Visibility, attrs: Vec<ast::Attribute>) -> P<ast::Item> {
        return P(ast::Item {
            ident: ctx.ext_cx.ident_of(&name),
            attrs: attrs,
            id: ast::DUMMY_NODE_ID,
            node: item,
            vis: vis,
            span: ctx.span
        });
    }

    let ci = Rc::new(RefCell::new(CompInfo::new(name.clone(), name.clone(), "".to_owned(), CompKind::Union, members.clone(), layout)));
    let union = TNamed(Rc::new(RefCell::new(TypeInfo::new(name.clone(), TComp(ci), layout))));

    // Nested composites may need to emit declarations and implementations as
    // they are encountered.  The declarations end up in 'extra' and are emitted
    // after the current union.
    let mut extra = vec!();

    let data_field_name = "_bindgen_data_";
    let data_field = mk_blob_field(ctx, data_field_name, layout);

    let def = ast::ItemStruct(
        ast::VariantData::Struct(vec![data_field], ast::DUMMY_NODE_ID),
        empty_generics()
    );
    let union_id = rust_type_id(ctx, name.clone());
    let union_attrs = vec!(mk_repr_attr(ctx, layout), mk_deriving_copy_attr(ctx));
    let union_def = mk_item(ctx, union_id, def, ast::Public, union_attrs);

    let union_impl = ast::ItemImpl(
        ast::Unsafety::Normal,
        ast::ImplPolarity::Positive,
        empty_generics(),
        None,
        P(cty_to_rs(ctx, &union, true)),
        gen_comp_methods(ctx, data_field_name, 0, CompKind::Union, &members, &mut extra),
    );

    let mut items = vec!(
        union_def,
        mk_item(ctx, "".to_string(), union_impl, ast::Inherited, Vec::new())
    );

    items.extend(extra.into_iter());
    items
}

fn const_to_rs(ctx: &mut GenCtx, name: String, val: i64, val_ty: ast::Ty) -> P<ast::Item> {
    let int_lit = ast::LitInt(
        val.abs() as u64,
        ast::UnsuffixedIntLit(if val < 0 { ast::Minus } else { ast::Plus })
            );

    let cst = ast::ItemConst(
        P(val_ty),
        ctx.ext_cx.expr_lit(ctx.span, int_lit)
            );

    let id = first(rust_id(ctx, name.clone()));
    P(ast::Item {
        ident: ctx.ext_cx.ident_of(&id[..]),
        attrs: Vec::new(),
        id: ast::DUMMY_NODE_ID,
        node: cst,
        vis: ast::Public,
        span: ctx.span
    })
}

fn cenum_to_rs(ctx: &mut GenCtx, name: String, comment: String, items: Vec<EnumItem>, layout: Layout) -> Vec<P<ast::Item>> {
    // Rust is not happy with univariant enums
    if items.len() < 2 {
        return vec!();
    }

    let variants = items.iter().map(|it| {
        let value_sign = ast::UnsuffixedIntLit(if it.val < 0 { ast::Minus } else { ast::Plus });
        let value_node =
            ast::ExprLit(P(respan(ctx.span, ast::LitInt(it.val.abs() as u64,
                                                        value_sign))));

        let variant = respan(ctx.span, ast::Variant_ {
            name: ctx.ext_cx.ident_of(&it.name),
            attrs: mk_doc_attr(ctx, it.comment.clone()),
            data: ast::VariantData::Unit(ast::DUMMY_NODE_ID),
            disr_expr: Some(P(ast::Expr {
                id: ast::DUMMY_NODE_ID,
                node: value_node,
                span: ctx.span,
                attrs: None,
            }))
        });
        P(variant)
    }).collect();

    let enum_ty = match layout.size {
        1 => "i8",
        2 => "i16",
        4 => "i32",
        8 => "i64",
        _ => "i32",
    };

    let mut attrs = mk_doc_attr(ctx, comment);
    attrs.push(respan(ctx.span, ast::Attribute_ {
        id: mk_attr_id(),
        style: ast::AttrStyle::Outer,
        value: P(respan(ctx.span, ast::MetaList(
            InternedString::new("repr"),
            vec!(P(respan(ctx.span,
                          ast::MetaWord(InternedString::new(enum_ty)))))
        ))),
        is_sugared_doc: false
    }));
    attrs.push(mk_deriving_copy_attr(ctx));

    vec!(P(ast::Item {
        ident: ctx.ext_cx.ident_of(&name),
        attrs: attrs,
        id: ast::DUMMY_NODE_ID,
        node: ast::ItemEnum(ast::EnumDef { variants: variants }, empty_generics()),
        vis: ast::Public,
        span: ctx.span
    }))
}

/// Generates accessors for fields in nested structs and unions which must be
/// represented in Rust as an untyped array.  This process may generate
/// declarations and implementations that must be placed at the root level.
/// These are emitted into `extra`.
fn gen_comp_methods(ctx: &mut GenCtx, data_field: &str, data_offset: usize,
                    kind: CompKind, members: &Vec<CompMember>,
                    extra: &mut Vec<P<ast::Item>>) -> Vec<P<ast::ImplItem>> {

    let mk_field_method = |ctx: &mut GenCtx, f: &FieldInfo, offset: usize| {
        // TODO: Implement bitfield accessors
        if f.bitfields.is_some() { return None; }

        let (f_name, _) = rust_id(ctx, f.name.clone());
        let ret_ty = P(cty_to_rs(ctx, &TPtr(Box::new(f.ty.clone()), false, false, Layout::zero()), true));

        // When the offset is zero, generate slightly prettier code.
        let method = {
            let impl_str = format!(r"
                impl X {{
                    pub unsafe fn {}(&mut self) -> {} {{
                        let raw: *mut u8 = ::std::mem::transmute(&self.{});
                        ::std::mem::transmute(raw.offset({}))
                    }}
                }}
            ", f_name, tts_to_string(&ret_ty.to_tokens(&ctx.ext_cx)[..]), data_field, offset);

            parse::new_parser_from_source_str(ctx.ext_cx.parse_sess(),
                ctx.ext_cx.cfg(), "".to_string(), impl_str).parse_item().unwrap().unwrap()
        };

        method.and_then(|i| {
            match i.node {
                ast::ItemImpl(_, _, _, _, _, mut items) => {
                    items.pop()
                }
                _ => unreachable!("impl parsed to something other than impl")
            }
        })
    };

    let mut offset = data_offset;
    let mut methods = vec!();
    for m in members.iter() {
        let advance_by = match m {
            &CompMember::Field(ref f) => {
                methods.extend(mk_field_method(ctx, f, offset).into_iter());
                f.ty.size()
            }
            &CompMember::Comp(ref rc_c) => {
                let ref c = rc_c.borrow();
                methods.extend(gen_comp_methods(ctx, data_field, offset, c.kind,
                                                &c.members, extra).into_iter());
                c.layout.size
            }
            &CompMember::CompField(ref rc_c, ref f) => {
                methods.extend(mk_field_method(ctx, f, offset).into_iter());

                let c = rc_c.borrow();
                extra.extend(comp_to_rs(ctx, comp_name(c.kind, &c.name), c.clone()).into_iter());
                f.ty.size()
            }
            &CompMember::Enum(_) => 0
        };
        match kind {
            CompKind::Struct => { offset += advance_by; }
            CompKind::Union  => { }
        }
    }
    methods
}

fn type_for_bitfield_width(ctx: &mut GenCtx, width: u32) -> ast::Ty {
    let input_type = if width > 16 {
        "u32"
    } else if width > 8 {
        "u16"
    } else if width > 1 {
        "u8"
    } else {
        "bool"
    };
    mk_ty(ctx, false, vec!(input_type.to_string()))
}

fn gen_bitfield_method(ctx: &mut GenCtx, bindgen_name: &String,
                       field_name: &String, field_type: &Type,
                       offset: usize, width: u32) -> ast::ImplItem {
    let input_type = type_for_bitfield_width(ctx, width);
    let field_type = cty_to_rs(ctx, &field_type, false);
    let setter_name = ctx.ext_cx.ident_of(&format!("set_{}", field_name));
    let bindgen_ident = ctx.ext_cx.ident_of(&*bindgen_name);

    let node = &quote_item!(&ctx.ext_cx,
        impl X {
            pub fn $setter_name(&mut self, val: $input_type) {
                self.$bindgen_ident &= !(((1 << $width) - 1) << $offset);
                self.$bindgen_ident |= (val as $field_type) << $offset;
            }
        }
    ).unwrap().node;
    match node {
        &ast::ItemImpl(_, _, _, _, _, ref items) => items[0].clone().and_then(|x| x),
        _ => unreachable!()
    }
}

fn gen_fullbitfield_method(ctx: &mut GenCtx, bindgen_name: &String,
                           field_type: &Type, bitfields: &[(String, u32)]) -> ast::ImplItem {
    let field_type = cty_to_rs(ctx, field_type, false);
    let mut args = vec!();
    let mut unnamed: usize = 0;
    for &(ref name, width) in bitfields.iter() {
        let ident = if name.is_empty() {
            unnamed += 1;
            let dummy = format!("unnamed_bitfield{}", unnamed);
            ctx.ext_cx.ident_of(&dummy)
        } else {
            ctx.ext_cx.ident_of(name)
        };
        args.push(ast::Arg {
            ty: P(type_for_bitfield_width(ctx, width)),
            pat: P(ast::Pat {
                id: ast::DUMMY_NODE_ID,
                node: ast::PatIdent(
                    ast::BindingMode::ByValue(ast::MutImmutable),
                    respan(ctx.span, ident),
                    None
                ),
                span: ctx.span
            }),
            id: ast::DUMMY_NODE_ID,
        });
    }

    let fndecl = ast::FnDecl {
        inputs: args,
        output: ast::Return(P(field_type.clone())),
        variadic: false
    };

    let stmts = Vec::with_capacity(bitfields.len() + 1);

    let mut offset = 0;
    let mut exprs = quote_expr!(&ctx.ext_cx, 0);
    let mut unnamed: usize = 0;
    for &(ref name, width) in bitfields.iter() {
        let name_ident = if name.is_empty() {
            unnamed += 1;
            let dummy = format!("unnamed_bitfield{}", unnamed);
            ctx.ext_cx.ident_of(&dummy)
        } else {
            ctx.ext_cx.ident_of(name)
        };
        exprs = quote_expr!(&ctx.ext_cx,
            $exprs | (($name_ident as $field_type) << $offset)
        );
        offset += width;
    }

    let block = ast::Block {
        stmts: stmts,
        expr: Some(exprs),
        id: ast::DUMMY_NODE_ID,
        rules: ast::DefaultBlock,
        span: ctx.span
    };

    let node = ast::ImplItemKind::Method(
        ast::MethodSig {
            unsafety: ast::Unsafety::Normal,
            abi: abi::Rust,
            decl: P(fndecl),
            generics: empty_generics(),
            explicit_self: respan(ctx.span, ast::SelfStatic),
            constness: ast::Constness::Const,
        }, P(block)
    );

    ast::ImplItem {
        id: ast::DUMMY_NODE_ID,
        ident: ctx.ext_cx.ident_of(&format!("new{}", bindgen_name)),
        vis: ast::Public,
        attrs: vec!(),
        node: node,
        span: ctx.span,
    }
}

fn mk_blob_field(ctx: &GenCtx, name: &str, layout: Layout) -> Spanned<ast::StructField_> {
    let ty_name = match layout.align {
        1 => "u8",
        2 => "u16",
        4 => "u32",
        8 => "u64",
        _ => "u8",
    };
    let data_len = if ty_name == "u8" { layout.size } else { layout.size / layout.align };

    let base_ty = mk_ty(ctx, false, vec!(ty_name.to_string()));
    let data_ty = if data_len == 1 {
        P(base_ty)
    } else {
        P(mk_arrty(ctx, &base_ty, data_len))
    };
    respan(ctx.span, ast::StructField_ {
        kind: ast::NamedField(
            ctx.ext_cx.ident_of(name),
            ast::Public,
        ),
        id: ast::DUMMY_NODE_ID,
        ty: data_ty,
        attrs: Vec::new()
    })
}

fn mk_link_name_attr(ctx: &mut GenCtx, name: String) -> ast::Attribute {
    let lit = respan(ctx.span, ast::LitStr(intern(&name).as_str(), ast::CookedStr));
    let attr_val = P(respan(ctx.span, ast::MetaNameValue(
        InternedString::new("link_name"), lit
    )));
    let attr = ast::Attribute_ {
        id: mk_attr_id(),
        style: ast::AttrStyle::Outer,
        value: attr_val,
        is_sugared_doc: false
    };
    respan(ctx.span, attr)
}

fn mk_repr_attr(ctx: &mut GenCtx, layout: Layout) -> ast::Attribute {
    let mut values = vec!(P(respan(ctx.span, ast::MetaWord(InternedString::new("C")))));
    if layout.packed {
        values.push(P(respan(ctx.span, ast::MetaWord(InternedString::new("packed")))));
    }
    let attr_val = P(respan(ctx.span, ast::MetaList(
        InternedString::new("repr"),
        values
    )));

    respan(ctx.span, ast::Attribute_ {
        id: mk_attr_id(),
        style: ast::AttrStyle::Outer,
        value: attr_val,
        is_sugared_doc: false
    })
}

fn mk_deriving_copy_attr(ctx: &mut GenCtx) -> ast::Attribute {
    let attr_val = P(respan(ctx.span, ast::MetaList(
        InternedString::new("derive"),
        vec!(P(respan(ctx.span, ast::MetaWord(InternedString::new("Copy")))),
             P(respan(ctx.span, ast::MetaWord(InternedString::new("Clone")))))
    )));

    respan(ctx.span, ast::Attribute_ {
        id: mk_attr_id(),
        style: ast::AttrStyle::Outer,
        value: attr_val,
        is_sugared_doc: false
    })
}

fn mk_unsafe_no_drop_flag_attr(ctx: &mut GenCtx) -> ast::Attribute {
    let attr_val = P(respan(ctx.span, ast::MetaWord(
        InternedString::new("unsafe_no_drop_flag")
    )));

    respan(ctx.span, ast::Attribute_ {
        id: mk_attr_id(),
        style: ast::AttrStyle::Outer,
        value: attr_val,
        is_sugared_doc: false
    })
}

fn mk_doc_attr(ctx: &mut GenCtx, doc: String) -> Vec<ast::Attribute> {
    if doc.is_empty() {
        return vec!();
    }

    let attr_val = P(respan(ctx.span, ast::MetaNameValue(
        InternedString::new("doc"),
        respan(ctx.span, ast::LitStr(intern(&doc).as_str(), ast::CookedStr))
    )));

    vec!(respan(ctx.span, ast::Attribute_ {
        id: mk_attr_id(),
        style: ast::AttrStyle::Outer,
        value: attr_val,
        is_sugared_doc: true
    }))
}

fn cvar_to_rs(ctx: &mut GenCtx, name: String,
                                mangled: String,
                                ty: &Type,
                                is_const: bool) -> P<ast::ForeignItem> {
    let (rust_name, was_mangled) = rust_id(ctx, name.clone());

    let mut attrs = Vec::new();
    if !mangled.is_empty() {
        attrs.push(mk_link_name_attr(ctx, mangled));
    } else if was_mangled {
        attrs.push(mk_link_name_attr(ctx, name));
    }

    let val_ty = P(cty_to_rs(ctx, ty, true));

    return P(ast::ForeignItem {
        ident: ctx.ext_cx.ident_of(&rust_name),
        attrs: attrs,
        node: ast::ForeignItemStatic(val_ty, !is_const),
        id: ast::DUMMY_NODE_ID,
        span: ctx.span,
        vis: ast::Public,
    });
}

fn cfuncty_to_rs(ctx: &mut GenCtx,
                 rty: &Type,
                 aty: &[(String, Type)],
                 var: bool) -> ast::FnDecl {

    let ret = match *rty {
        TVoid => ast::DefaultReturn(ctx.span),
        // Disable references in returns for now
        TPtr(ref t, is_const, _, ref layout) =>
            ast::Return(P(cty_to_rs(ctx, &TPtr(t.clone(), is_const, false, layout.clone()), true))),
        _ => ast::Return(P(cty_to_rs(ctx, rty, true)))
    };

    let mut unnamed: usize = 0;
    let args: Vec<ast::Arg> = aty.iter().map(|arg| {
        let (ref n, ref t) = *arg;

        let arg_name = if n.is_empty() {
            unnamed += 1;
            format!("arg{}", unnamed)
        } else {
            first(rust_id(ctx, n.clone()))
        };

        // From the C90 standard (http://c0x.coding-guidelines.com/6.7.5.3.html)
        // 1598 - A declaration of a parameter as “array of type” shall be
        // adjusted to “qualified pointer to type”, where the type qualifiers
        // (if any) are those specified within the [ and ] of the array type
        // derivation.
        let arg_ty = P(match t {
            &TArray(ref typ, _, ref l) => cty_to_rs(ctx, &TPtr(typ.clone(), false, false, l.clone()), true),
            _ => cty_to_rs(ctx, t, true),
        });

        ast::Arg {
            ty: arg_ty,
            pat: P(ast::Pat {
                 id: ast::DUMMY_NODE_ID,
                 node: ast::PatIdent(
                     ast::BindingMode::ByValue(ast::MutImmutable),
                     respan(ctx.span, ctx.ext_cx.ident_of(&arg_name)),
                     None
                 ),
                 span: ctx.span
            }),
            id: ast::DUMMY_NODE_ID,
        }
    }).collect();

    let var = !args.is_empty() && var;
    return ast::FnDecl {
        inputs: args,
        output: ret,
        variadic: var
    };
}

fn cfunc_to_rs(ctx: &mut GenCtx,
               name: String,
               mangled: String,
               comment: String,
               rty: &Type,
               aty: &[(String, Type)],
               var: bool,
               vis: ast::Visibility) -> P<ast::ForeignItem> {
    let var = !aty.is_empty() && var;
    let decl = ast::ForeignItemFn(
        P(cfuncty_to_rs(ctx, rty, aty, var)),
        empty_generics()
    );

    let (rust_name, was_mangled) = rust_id(ctx, name.clone());

    let mut attrs = mk_doc_attr(ctx, comment);
    if !mangled.is_empty() {
        attrs.push(mk_link_name_attr(ctx, mangled));
    } else if was_mangled {
        attrs.push(mk_link_name_attr(ctx, name));
    }

    return P(ast::ForeignItem {
              ident: ctx.ext_cx.ident_of(&rust_name),
              attrs: attrs,
              node: decl,
              id: ast::DUMMY_NODE_ID,
              span: ctx.span,
              vis: vis,
           });
}

fn cty_to_rs(ctx: &mut GenCtx, ty: &Type, allow_bool: bool) -> ast::Ty {
    return match ty {
        &TVoid => mk_ty(ctx, true, vec!("libc".to_string(), "c_void".to_string())),
        &TInt(i, ref layout) => match i {
            IBool => {
                let ty_name = match layout.size {
                    1 if allow_bool => "bool",
                    2 => "u16",
                    4 => "u32",
                    8 => "u64",
                    _ => "u8",
                };
                mk_ty(ctx, false, vec!(ty_name.to_string()))
            },
            ISChar => mk_ty(ctx, true, vec!("libc".to_string(), "c_char".to_string())),
            IInt |
            IShort |
            ILongLong => mk_ty(ctx, false, vec!(format!("i{}", layout.size * 8))),
            IUChar |
            IUInt |
            IUShort |
            IULongLong => mk_ty(ctx, false, vec!(format!("u{}", layout.size * 8))),
            ILong => mk_ty(ctx, true, vec!("libc".to_string(), "c_long".to_string())),
            IULong => mk_ty(ctx, true, vec!("libc".to_string(), "c_ulong".to_string())),
        },
        &TFloat(f, _) => match f {
            FFloat => mk_ty(ctx, false, vec!("f32".to_string())),
            FDouble => mk_ty(ctx, false, vec!("f64".to_string()))
        },
        &TPtr(ref t, is_const, _is_ref, _) => {
            let id = cty_to_rs(ctx, &**t, allow_bool);
/*
            if is_ref {
                mk_refty(ctx, &id, is_const)
            } else {
*/
                mk_ptrty(ctx, &id, is_const)
//            }
        },
        &TArray(ref t, s, _) => {
            let ty = cty_to_rs(ctx, &**t, allow_bool);
            mk_arrty(ctx, &ty, s)
        },
        &TFuncPtr(ref sig) => {
            let decl = cfuncty_to_rs(ctx, &*sig.ret_ty, &sig.args[..], sig.is_variadic);
            mk_fnty(ctx, &decl, sig.abi)
        },
        &TFuncProto(ref sig) => {
            let decl = cfuncty_to_rs(ctx, &*sig.ret_ty, &sig.args[..], sig.is_variadic);
            mk_fn_proto_ty(ctx, &decl, sig.abi)
        },
        &TNamed(ref ti) => {
            let id = rust_type_id(ctx, ti.borrow().name.clone());
            mk_ty(ctx, false, vec!(id))
        },
        &TComp(ref ci) => {
            let mut c = ci.borrow_mut();
            c.name = unnamed_name(ctx, c.name.clone(), c.filename.clone());
            let args = c.args.iter().map(|gt| {
                P(cty_to_rs(ctx, gt, allow_bool))
            }).collect();
            mk_ty_args(ctx, false, vec!(comp_name(c.kind, &c.name)), args)
        },
        &TEnum(ref ei) => {
            let mut e = ei.borrow_mut();
            e.name = unnamed_name(ctx, e.name.clone(), e.filename.clone());
            mk_ty(ctx, false, vec!(enum_name(&e.name)))
        }
    };
}

fn cty_is_translatable(ty: &Type) -> bool {
    match ty {
        &TVoid => false,
        &TArray(ref t, _, _) => {
            cty_is_translatable(&**t)
        },
        &TComp(ref ci) => {
            let c = ci.borrow();
            !c.args.iter().any(|gt| gt == &TVoid)
        },
        _ => true,
    }
}

fn cty_has_destructor(ty: &Type) -> bool {
    match ty {
        &TArray(ref t, _, _) => {
            cty_has_destructor(&**t)
        }
        &TComp(ref ci) => {
            let c = ci.borrow();
            if c.has_destructor || c.members.iter().any(|f| match f {
                &CompMember::Field(ref f) |
                &CompMember::CompField(_, ref f) =>
                    cty_has_destructor(&f.ty),
                _ => false,
            }) {
                return true;
            }
            if let Some(ref ty) = c.ref_template {
                true
            } else {
                false
            }
        },
        &TNamed(ref ti) => {
            cty_has_destructor(&ti.borrow().ty)
        },
        _ => false,
    }
}

fn mk_ty(ctx: &GenCtx, global: bool, segments: Vec<String>) -> ast::Ty {
    mk_ty_args(ctx, global, segments, vec!())
}

fn mk_ty_args(ctx: &GenCtx, global: bool, segments: Vec<String>, args: Vec<P<ast::Ty>>) -> ast::Ty {
    let ty = ast::TyPath(
        None,
        ast::Path {
            span: ctx.span,
            global: global,
            segments: segments.iter().map(|s| {
                ast::PathSegment {
                    identifier: ctx.ext_cx.ident_of(s),
                    parameters: ast::AngleBracketedParameters(ast::AngleBracketedParameterData {
                        lifetimes: vec!(),
                        types: OwnedSlice::from_vec(args.clone()),
                        bindings: OwnedSlice::empty(),
                    }),
                }
            }).collect()
        },
    );

    return ast::Ty {
        id: ast::DUMMY_NODE_ID,
        node: ty,
        span: ctx.span
    };
}

fn mk_ptrty(ctx: &mut GenCtx, base: &ast::Ty, is_const: bool) -> ast::Ty {
    let ty = ast::TyPtr(ast::MutTy {
        ty: P(base.clone()),
        mutbl: if is_const { ast::MutImmutable } else { ast::MutMutable }
    });

    return ast::Ty {
        id: ast::DUMMY_NODE_ID,
        node: ty,
        span: ctx.span
    };
}

fn mk_refty(ctx: &mut GenCtx, base: &ast::Ty, is_const: bool) -> ast::Ty {
    let ty = ast::TyRptr(
        None,
        ast::MutTy {
            ty: P(base.clone()),
            mutbl: if is_const { ast::MutImmutable } else { ast::MutMutable }
        }
    );

    return ast::Ty {
        id: ast::DUMMY_NODE_ID,
        node: ty,
        span: ctx.span
    };
}

fn mk_arrty(ctx: &GenCtx, base: &ast::Ty, n: usize) -> ast::Ty {
    let int_lit = ast::LitInt(n as u64, ast::UnsignedIntLit(ast::TyUs));
    let sz = ast::ExprLit(P(respan(ctx.span, int_lit)));
    let ty = ast::TyFixedLengthVec(
        P(base.clone()),
        P(ast::Expr {
            id: ast::DUMMY_NODE_ID,
            node: sz,
            span: ctx.span,
            attrs: None,
        })
    );

    return ast::Ty {
        id: ast::DUMMY_NODE_ID,
        node: ty,
        span: ctx.span
    };
}

fn mk_fn_proto_ty(ctx: &mut GenCtx, decl: &ast::FnDecl, abi: abi::Abi) -> ast::Ty {
    let fnty = ast::TyBareFn(P(ast::BareFnTy {
        unsafety: ast::Unsafety::Normal,
        abi: abi,
        lifetimes: Vec::new(),
        decl: P(decl.clone())
    }));

    ast::Ty {
        id: ast::DUMMY_NODE_ID,
        node: fnty,
        span: ctx.span,
    }
}

fn mk_fnty(ctx: &mut GenCtx, decl: &ast::FnDecl, abi: abi::Abi) -> ast::Ty {
    let fnty = ast::TyBareFn(P(ast::BareFnTy {
        unsafety: ast::Unsafety::Unsafe,
        abi: abi,
        lifetimes: Vec::new(),
        decl: P(decl.clone())
    }));

    let segs = vec![
        ast::PathSegment {
            identifier: ctx.ext_cx.ident_of("std"),
            parameters: ast::AngleBracketedParameters(ast::AngleBracketedParameterData {
                lifetimes: Vec::new(),
                types: OwnedSlice::empty(),
                bindings: OwnedSlice::empty(),
            }),
        },
        ast::PathSegment {
            identifier: ctx.ext_cx.ident_of("option"),
            parameters: ast::AngleBracketedParameters(ast::AngleBracketedParameterData {
                lifetimes: Vec::new(),
                types: OwnedSlice::empty(),
                bindings: OwnedSlice::empty(),
            }),
        },
        ast::PathSegment {
            identifier: ctx.ext_cx.ident_of("Option"),
            parameters: ast::AngleBracketedParameters(ast::AngleBracketedParameterData {
                lifetimes: Vec::new(),
                types: OwnedSlice::from_vec(vec!(
                    P(ast::Ty {
                        id: ast::DUMMY_NODE_ID,
                        node: fnty,
                        span: ctx.span
                    })
                )),
                bindings: OwnedSlice::empty(),
            }),
        }
    ];

    return ast::Ty {
        id: ast::DUMMY_NODE_ID,
        node: ast::TyPath(
            None,
            ast::Path {
                span: ctx.span,
                global: true,
                segments: segs
            },
        ),
        span: ctx.span
    };
}
