// njn: qual
#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    Hash,
    rustc_macros::HashStable,
    rustc_macros::Encodable,
    rustc_macros::Decodable
)]
pub struct Csa {
    pub c_variadic: bool,
    pub safety: rustc_hir::Safety,
    pub abi: rustc_target::spec::abi::Abi,
}
