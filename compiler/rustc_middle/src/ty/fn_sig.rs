//use rustc_type_ir::Interner;
//use crate::ty::{Binder, Ty, TyCtxt, TyDecoder, TyEncoder};
use crate::ty::{List, Ty, TyCtxt};
use rustc_type_ir::inherent::Tys;
//use rustc_serialize::{Decodable, Encodable};

// njn: qual everywhere in this file

// njn: derive Debug? or use the handwritten one?
#[derive(
    Clone,
    Copy,
    PartialEq,
    Eq,
    Hash,
    rustc_macros::HashStable,
    rustc_macros::TyEncodable,
    rustc_macros::TyDecodable,
    rustc_macros::TypeFoldable,
    rustc_macros::TypeVisitable
)]
pub struct FnSig<'tcx> {
    pub inputs_and_output: &'tcx List<Ty<'tcx>>,
    pub c_variadic: bool,
    pub safety: rustc_hir::Safety,
    pub abi: rustc_target::spec::abi::Abi,
}

// njn: duplicates the `rustc_type_ir::inherent::FnSig` impl methods...
impl<'tcx> FnSig<'tcx> {
    pub fn inputs_and_output(self) -> &'tcx List<Ty<'tcx>> {
        self.inputs_and_output
    }

    pub fn inputs(self) -> &'tcx [Ty<'tcx>] {
        self.inputs_and_output.inputs()
    }

    pub fn output(self) -> Ty<'tcx> {
        self.inputs_and_output.output()
    }
}

// njn: can I auto-derive this somehow?
impl<'a, 'tcx> crate::ty::Lift<TyCtxt<'tcx>> for FnSig<'a> {
    type Lifted = FnSig<'tcx>;

    fn lift_to_tcx(self, tcx: TyCtxt<'tcx>) -> Option<Self::Lifted> {
        Some(FnSig {
            inputs_and_output: self.inputs_and_output.lift_to_tcx(tcx)?,
            c_variadic: self.c_variadic,
            safety: self.safety,
            abi: self.abi,
        })
    }
}

// njn: remove?
impl<'tcx> rustc_errors::IntoDiagArg for FnSig<'tcx> {
    fn into_diag_arg(self) -> rustc_errors::DiagArgValue {
        format!("{self:?}").into_diag_arg()
    }
}
