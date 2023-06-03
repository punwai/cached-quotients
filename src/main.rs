use ark_ec::{scalar_mul::variable_base::{VariableBaseMSM}, bls12::G1Prepared, Group, short_weierstrass::{SWCurveConfig, Projective}};
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain, EvaluationDomain, DenseUVPolynomial, domain, Polynomial};
use ark_bls12_381::{G1Projective as G1, G2Projective as G2, Fr as F, G1Affine, G2Affine};
use ark_std::rand::distributions::Distribution;
use ark_relations::r1cs::Field;
use ark_std::{Zero, One};
use std::{ops::{Mul, Sub, Neg}, time::Instant};

struct TrustedSetupParams {
    g1s: Vec<G1>,
    g2s: Vec<G2>
}

impl TrustedSetupParams {
    fn new(table_size: u64) -> Self {
        let g1s = vec![];
        let g2s = vec![];
        // TODO: SWITCH X TO SOMETHING THAT IS ACTUALLY RANDOM
        let x = F::from(12345);
        let x_ptr = F::one();
        for i in 0..table_size {
            g1s.push(G1::generator() * x_ptr);
            g2s.push(G2::generator() * x_ptr);
            x_ptr *= x;
        }
        Self {
            g1s,
            g2s
        }
    }
}

fn commit_g1(coeffs: Vec<F>, srs: TrustedSetupParams) -> G1 {
    G1::msm(
        &srs.g1s[..coeffs.len()].iter().map(|x| G1Affine::from(*x)).collect::<Vec<_>>(),
        &coeffs
    ).unwrap()
}

fn commit_g2(coeffs: Vec<F>, srs: TrustedSetupParams) -> G2 {
    G2::msm(
        &srs.g2s[..coeffs.len()].iter().map(|x| G2Affine::from(*x)).collect::<Vec<_>>(),
        &coeffs
    ).unwrap()
}

fn setup(N: u64, t: Vec<F>) {
    let srs = TrustedSetupParams::new(N);
    let domain = GeneralEvaluationDomain::<F>::new(N as usize).unwrap();
    let T = domain.ifft(&t);
    let t_commit = commit_g2(T, srs);

    for i in 0..N { }
}

fn round_1() {

}

fn round_2() {

}

fn round_3() {

}

fn main() {
    setup();
    round_1();
    round_2();
    round_3();
}
