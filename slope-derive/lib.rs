use proc_macro2::TokenStream;
use quote::quote;
use synstructure::{decl_derive, Structure};

decl_derive!([Trace] => trace_derive);
decl_derive!([Root] => root_derive);

fn trace_derive(mut strc: Structure) -> TokenStream {
    strc.underscore_const(true);

    let body = strc.each(|binding| {
        quote! {
            Trace::trace(#binding, tracer);
        }
    });

    strc.gen_impl(quote! {
        use ::slope_types::{Trace, Tracer};

        gen unsafe impl Trace for @Self {
            fn trace(&self, tracer: &mut impl Tracer) {
                match *self { #body }
            }
        }
    })
}

fn root_derive(mut strc: Structure) -> TokenStream {
    strc.underscore_const(true);

    let name = &strc.ast().ident;
    let name = quote! {
        #name
    };

    let vis = match &strc.ast().vis {
        syn::Visibility::Public(_) => quote!(pub),
        syn::Visibility::Crate(_) => quote!(pub(crate)),
        syn::Visibility::Restricted(_) => quote!(pub(super)),
        syn::Visibility::Inherited => quote!(pub(super)),
    };

    // Use inner module to make sure the root's fields are private even in
    // the same module.
    quote! {
        mod root {
            use ::slope_types::{Root, Parameters, Heap, MutationContext, AllocationContext};
            use ::std::mem::transmute;

            impl<'gc> Root for super::#name<'gc> {
                type Rooted = Rooted<'gc>;

                fn root(parameters: Parameters) -> Self::Rooted {
                    Rooted {
                        root: Self::default(),
                        heap: Heap::with_parameters(parameters),
                    }
                }
            }

            #vis struct Rooted<'gc> {
                root: super::#name<'gc>,
                heap: Heap,
            }

            impl Rooted<'_> {
                pub fn mutate<'gc>(&'gc mut self) -> MutationContext<'gc, super::#name<'gc>> {
                    unsafe { MutationContext::for_root(transmute(&mut self.root)) }
                }

                pub fn mutate_alloc<'gc>(&'gc mut self) -> AllocationContext<'gc, super::#name<'gc>> {
                    unsafe { AllocationContext::for_root(transmute(&mut self.root), &mut self.heap) }
                }
            }
        }
    }
}
