#include <lean/lean.h>

// Later : Sort u → Sort u
// Later α = PUnit -> α

// next {α : Sort u} (a : PUnit → α) : Later α
extern "C" lean_obj_res igdtt_next(lean_object* thunk /* : PUnit → α */) {
  return thunk /* : Later α */; // TODO: memoise?
}

lean_obj_res igdtt_ap_impl(lean_object* f /*  : Later (α → β) */, lean_object* a /* : Later α */, lean_object* unit /* : PUnit */) {
  // fun f a u => f u (a u)
  return lean_apply_2(f, unit, lean_apply_1(a, unit));
}
// ap {α β : Sort u} (f : Later (α → β)) (a : Later α) : Later β
extern "C" lean_obj_res igdtt_ap(lean_object* f /*  : Later (α → β) */, lean_object* a /* : Later α */) {
  lean_inc(f);
  lean_inc(a);
  lean_obj_res clo = lean_alloc_closure((void*)igdtt_ap_impl, 3, 2);
  lean_closure_set(clo, 0, f);
  lean_closure_set(clo, 1, a);
  return clo;
}

extern "C" lean_obj_res igdtt_gfix(lean_object*);
lean_obj_res igdtt_gfix_arg(lean_object* f /* : Later α → α */, lean_object* unit) {
  return igdtt_gfix(f);
}
lean_obj_res igdtt_gfix(lean_object* f /* : Later α → α */) {
  // fun f => f (next (fun () => gfix f))
  // = { next = id }
  // fun f => f (fun () => gfix f)
  lean_obj_res arg = lean_alloc_closure((void*)igdtt_gfix_arg, 2, 1);
  // TODO: use same allocation of arg over multiple iterations?
  //       Probably impossible; arg would become cyclic. (Would that be bad?)
  lean_closure_set(arg, 0, f);
  return lean_apply_1(f, arg);
}

lean_obj_res igdtt_flip_impl(lean_object* f /* : α → Later β */, lean_object* unit, lean_object* a) {
  // fun f u a => f a u
  return lean_apply_2(f, a, unit);
}
extern "C" lean_obj_res igdtt_flip(lean_object* f) {
  // fun f u a => f a u, but arity 1 
  lean_obj_res pap = lean_alloc_closure((void*)igdtt_flip_impl, 3, 1);
  lean_inc(f);
  lean_closure_set(pap, 0, f);
  return pap;
}

extern "C" lean_obj_res igdtt_force(lean_object* thunk) {
  return lean_apply_1(thunk, lean_box(0));
}
