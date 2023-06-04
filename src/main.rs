use ark_ec::{scalar_mul::variable_base::{VariableBaseMSM}, bls12::G1Prepared, Group, short_weierstrass::{SWCurveConfig, Projective}};
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain, EvaluationDomain, DenseUVPolynomial, domain, Polynomial};
use ark_bls12_381::{G1Projective as G1, G2Projective as G2, Fr as F, G1Affine, G2Affine};
use ark_std::rand::distributions::Distribution;
use ark_relations::r1cs::Field;
use ark_std::{Zero, One};
use std::{ops::{Mul, Sub, Neg}, time::Instant, iter::Map, collections::HashMap};
use rand::{rngs::OsRng, Rng};


struct TrustedSetupParams {
    g1s: Vec<G1>,
    g2s: Vec<G2>
}

// 

impl TrustedSetupParams {
    fn new(table_size: u64) -> Self {
        let mut g1s = vec![];
        let mut g2s = vec![];

        // TODO: SWITCH X TO SOMETHING THAT IS ACTUALLY RANDOM
        let x = F::from(OsRng.gen::<u64>());

        let mut x_ptr = F::one();
        for i in 0..(table_size + 5) {
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

fn commit_g1(coeffs: &[F], srs: &TrustedSetupParams) -> G1 {
    G1::msm(
        &srs.g1s[..coeffs.len()].iter().map(|x| G1Affine::from(*x)).collect::<Vec<_>>(),
        &coeffs
    ).unwrap()
}

fn commit_g2(coeffs: &[F], srs: &TrustedSetupParams) -> G2 {
    G2::msm(
        &srs.g2s[..coeffs.len()].iter().map(|x| G2Affine::from(*x)).collect::<Vec<_>>(),
        &coeffs
    ).unwrap()
}

struct GenOutput {
    N: u64,
    srs: TrustedSetupParams,
    z_commit: G2,
    t_commit: G2,
    qi_commits: Vec<G1>,
    Li_commits: Vec<G1>,
    Li_shifted_commits: Vec<G1>,
    cofactor: F
}

// Takes a bunch of coefficients and extends the basis by 4x
fn extend_lagrange_basis(n: usize, evals: &[F], cofactor: &F) -> Vec<F> {
    let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let group_order = domain.size();
    let mut coeffs = domain.ifft(evals)
        .into_iter()
        .enumerate()
        .map(|(i, x)| x * &cofactor.pow(vec![i as u64]))
        .collect::<Vec<_>>();
    domain.fft(&coeffs)
}

fn extended_bases_to_coeffs(n: usize, evals: &[F], cofactor: &F) -> Vec<F> {
    let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let group_order = domain.size();
    let inv_offset = F::one() / cofactor;
    domain.ifft(&evals)
        .iter()
        .enumerate()
        .map(|(i, x)| x * &cofactor.pow(vec![i as u64]))
        .collect::<Vec<_>>()
}

fn setup(N: u64, t: &Vec<F>) -> GenOutput {
    let srs = TrustedSetupParams::new(N);
    let domain = GeneralEvaluationDomain::<F>::new(N as usize).unwrap();
    let group_order = domain.size();

    let z_commit = srs.g2s[N as usize] - G2::generator();

    let T = domain.ifft(&t);
    let t_commit = commit_g2(&T, &srs);
    let mut Li_commits = vec![];
    let mut Li_shifted_commits = vec![];

    for i in 0..(N as usize) {
        // Commit to the Lagrange polynomials
        let mut L_eval = vec![F::zero(); N as usize];
        L_eval[i] = F::one();
        let L_i = domain.ifft(&t);
        Li_commits.push(commit_g1(&L_i, &srs));
        // Commit to (L_i(x) - L(0) / x)
        Li_shifted_commits.push(commit_g1(&L_i[1..(N as usize)], &srs)); // Compute Q_i(x)
    }
    
    // Scale each of the K_i through scalar multiplication
    let cofactor = F::from(123456);
    let t_shifted = extend_lagrange_basis(N as usize, &t, &cofactor);


    let w = domain.group_gen();
    let mut w_ptr = F::one();
    let mut committed_quotients = vec![];

    for i in 0..(N as usize) {
        let Z_V = w / &F::from(N);
        let mut w_inner_ptr = F::one();
        let mut q_evals = vec![];

        for j in 0..t_shifted.len() {
            let eval = (t_shifted[j] - t[j]) / (Z_V * w_inner_ptr);
            q_evals.push(eval);
            w_inner_ptr *= w;
        }
        w_ptr *= w;
        // Q polynomial 
        let q_poly = extended_bases_to_coeffs(N as usize, &q_evals, &cofactor);
        // evaluate
        let q_i = commit_g1(&q_poly, &srs);
        committed_quotients.push(q_i);
    }

    GenOutput { 
        N,
        srs,
        z_commit,
        t_commit, 
        qi_commits: committed_quotients, 
        Li_commits,
        Li_shifted_commits,
        cofactor
    }
}

struct Transcript {
    // SPARSE LAGRANGIAN (index, value)
    m: Option<Vec<(u64, F)>>
}

impl Transcript {
    fn new() -> Self {
        Self {
            m: None
        }
    }
}
struct Round1Message {
    m: G1,
}

struct Round2Message { }

struct Round3Message { }

fn round_1(f: &Vec<F>, t: &Vec<F>, gen: &GenOutput, transcript: &mut Transcript) -> Round1Message {
    let mut map = HashMap::new();
    for f_el in f {
        let count = map.entry(f_el).or_insert(0);
        *count += 1;
    }
    let mut m_commit = G1::zero();

    let mut m = Vec::new();
    for (ix, t_el) in t.iter().enumerate() {
        if let Some(count) = map.get_mut(&t_el) {
            m_commit += gen.srs.g1s[ix] * &F::from(*count);
            m.push((ix as u64, F::from(*count)));
        }
    }
    transcript.m = Some(m);
    Round1Message { m: m_commit }
}

fn round_2(f: Vec<F>, t: Vec<F>, beta: F, transcript: &mut Transcript, gen: &GenOutput) -> Round2Message {
    let m = transcript.m.clone().unwrap();
    let mut a_commit = G1::zero();
    for (ix, m_el) in m.iter() {
        a_commit += &(gen.Li_commits[*ix as usize] * (m_el / &(t[*ix as usize] + beta)));
    }
    let mut q_commit = G1::zero();
    for (ix, m_el) in m.iter() {
        let a_i = (m_el) / &(t[*ix as usize] + beta);
        q_commit += &(gen.qi_commits[*ix as usize] * a_i);
    }
    // Compute Bs
    let domain = GeneralEvaluationDomain::<F>::new(f.len()).unwrap();
    let b_evals = f.iter().map(|f_el| F::one() / (f_el + &beta)).collect::<Vec<_>>();
    let b_poly = domain.ifft(&b_evals);
    let b_0 = b_poly.clone().into_iter().skip(1).collect::<Vec<_>>();
    let b_0_committed = commit_g1(&b_0, &gen.srs);
    // Compute Q_B(X)W
    let n = f.len();
    let extended_b = extend_lagrange_basis(n, &b_evals, &gen.cofactor);
    let extended_f = extend_lagrange_basis(n, &f, &gen.cofactor);
    // I don't think this is necessary and can be computed without FFTs.
    let vanishing_evals = vec![F::zero(); n];
    let extended_z = extend_lagrange_basis(n, &vanishing_evals, &gen.cofactor);
    let q_B_evals = (0..n).map(|i| (extended_b[i] * (extended_f[i] + beta) - F::one()) / &extended_z[i]).collect::<Vec<_>>();
    // Instead of this we can actually do an MSM with the committed Lagrangian bases
    let q_B = domain.ifft(&q_B_evals);
    let q_B_commit = commit_g1(&q_B, &gen.srs);
    let N: usize = t.len();
    let mut P_poly = vec![F::zero(); N - 1 - (n - 2)];
    P_poly.extend(b_0);
    let p_commit = commit_g1(&P_poly, &gen.srs);
    Round2Message {  }
}

fn round_3() {

}

fn main() {
    // setup();
    let convert_ff = |x: Vec<u64>| x.into_iter().map(|x| F::from(x)).collect::<Vec<_>>();
    let f_vec = convert_ff(vec![1, 2, 3, 4]);
    let t_vec = convert_ff(vec![1, 2, 3, 4, 5, 6, 7, 8]);

    let N = t_vec.len();
    let n = t_vec.len();

    let gen = setup(N as u64, &t_vec);
    let mut transcript = Transcript::new();
    round_1(&f_vec, &t_vec, &gen, &mut transcript);
    // round_2();
    // round_3();
}
