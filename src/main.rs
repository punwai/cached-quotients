use ark_ec::{scalar_mul::variable_base::{VariableBaseMSM}, bls12::G1Prepared, Group, short_weierstrass::{SWCurveConfig, Projective}, pairing::{self, Pairing}, PairingFriendlyCycle};
use ark_poly::{univariate::{DensePolynomial, DenseOrSparsePolynomial}, GeneralEvaluationDomain, EvaluationDomain, DenseUVPolynomial, domain, Polynomial};
use ark_bls12_381::{G1Projective as G1, G2Projective as G2, Fr as F, G1Affine, G2Affine, Bls12_381};
use ark_std::rand::distributions::Distribution;
use ark_relations::r1cs::Field;
use ark_std::{Zero, One};
use std::{ops::{Mul, Sub, Neg}, time::Instant, iter::Map, collections::HashMap};
use rand::{rngs::OsRng, Rng};
use ark_std::UniformRand;

struct TrustedSetupParams {
    g1s: Vec<G1>,
    g2s: Vec<G2>,
}

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

fn commit_g1_lagrange(evals: &[F], gen: &GenOutput) -> G1 {
    G1::msm(
        &gen.Li_commits[..evals.len()].iter().map(|x| G1Affine::from(*x)).collect::<Vec<_>>(),
        &evals
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
    qis: Vec<DensePolynomial<F>>,
    qi_commits: Vec<G1>,
    Li_commits: Vec<G1>,
    Lis: Vec<DensePolynomial<F>>,
    Li_shifted_commits: Vec<G1>,
    Li_constants: Vec<F>,
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
    let mut Li_constants = vec![];
    let mut Lis = vec![];

    for i in 0..(N as usize) {
        // Commit to the Lagrange polynomials
        let mut L_eval = vec![F::zero(); N as usize];
        L_eval[i] = F::one();

        let L_i = domain.ifft(&L_eval);
        let Li_constant = L_i[0];
        Li_constants.push(Li_constant);

        Li_commits.push(commit_g1(&L_i, &srs));
        // Commit to (L_i(x) - L(0) / x)
        Li_shifted_commits.push(commit_g1(&L_i[1..(N as usize)], &srs)); // Compute Q_i(x)
        Lis.push(DensePolynomial { coeffs: L_i } );
    }
    
    // Scale each of the K_i through scalar multiplication
    let cofactor = F::from(123456);
    let t_shifted = extend_lagrange_basis(N as usize, &t, &cofactor);


    let w = F::one();
    let mut w_ptr = domain.group_gen();
    let mut committed_quotients = vec![];
    let mut qis = vec![];

    for i in 0..(N as usize) {
        let Z_V = (w * cofactor) / &F::from(N);
        let mut w_inner_ptr = F::one();
        let mut q_evals = vec![];

        for j in 0..t_shifted.len() {
            let eval = (t_shifted[j] - t[i]) / (Z_V * (w_inner_ptr * cofactor - w_ptr));
            q_evals.push(eval);
            w_inner_ptr *= w;
        }
        w_ptr *= w;
        // Q polynomial 
        let q_poly = extended_bases_to_coeffs(N as usize, &q_evals, &cofactor);
        // evaluate
        let q_i = commit_g1(&q_poly, &srs);
        qis.push(DensePolynomial {coeffs: q_poly });
        committed_quotients.push(q_i);
    }

    GenOutput { 
        N,
        srs,
        z_commit,
        t_commit, 
        qi_commits: committed_quotients, 
        qis,
        Lis,
        Li_commits,
        Li_shifted_commits,
        Li_constants,
        cofactor
    }
}

struct Transcript {
    // SPARSE LAGRANGIAN (index, value)
    m: Option<Vec<(u64, F)>>,
    b0: Option<DensePolynomial<F>>,
    // q_A: Option<DensePolynomial<F>>,
    q_B: Option<DensePolynomial<F>>,
    q_B_evals: Option<Vec<F>>,
    beta: Option<F>,
    gamma: Option<F>,
    eta: Option<F>,
}

impl Transcript {
    fn new() -> Self {
        Self {
            m: None,
            b0: None,
            beta: None,
            gamma: None,
            eta: None,
            q_B: None,
            q_B_evals: None,
        }
    }
}
struct Round1Message {
    m: G1,
}

struct Round2Message {
    a: G1,
    q_a: G1,
    b_0_commit: G1,
    p_commit: G1,
}

struct Round3Message { }

fn round_1(f: &Vec<F>, t: &Vec<F>, transcript: &mut Transcript, gen: &GenOutput) -> Round1Message {
    let mut map = HashMap::new();

    for f_el in f {
        let count = map.entry(f_el).or_insert(0);
        *count += 1;
    }
    let mut m_commit = G1::zero();

    let mut m = Vec::new();
    for (ix, t_el) in t.iter().enumerate() {
        if let Some(count) = map.get_mut(&t_el) {
            m_commit += gen.Li_commits[ix] * &F::from(*count);
            m.push((ix as u64, F::from(*count)));
        }
    }
    transcript.m = Some(m);
    Round1Message { m: m_commit }
}

fn round_2(f: &Vec<F>, t: &Vec<F>, transcript: &mut Transcript, gen: &GenOutput) -> Round2Message {
    let beta = transcript.beta.clone().unwrap();
    let m = transcript.m.clone().unwrap();
    let mut a_commit = G1::zero();
    println!("ckpoint 1");
    for (ix, m_el) in m.iter() {
        a_commit += &(gen.Li_commits[*ix as usize] * (m_el / &(t[*ix as usize] + beta)));
    }
    println!("ckpoint 2");
    let mut q_commit = G1::zero();
    for (ix, m_el) in m.iter() {
        let a_i = (m_el) / &(t[*ix as usize] + beta);
        q_commit += &(gen.qi_commits[*ix as usize] * a_i);
    }
    println!("ckpoint 3");
    // Compute Bs
    let domain = GeneralEvaluationDomain::<F>::new(f.len()).unwrap();
    let b_evals = f.iter().map(|f_el| F::one() / (f_el + &beta)).collect::<Vec<_>>();

    println!("ckpoint 4");
    let b_poly = domain.ifft(&b_evals);
    let b_0 = b_poly.clone().into_iter().skip(1).collect::<Vec<_>>();

    let b_0_commit = commit_g1(&b_0, &gen.srs);
    // Compute Q_B(X)W
    let n = f.len();
    let extended_b = extend_lagrange_basis(n, &b_evals, &gen.cofactor);
    let extended_f = extend_lagrange_basis(n, &f, &gen.cofactor);
    // I don't think this is necessary and can be computed without FFTs.
    // This is actually fucking broken, this is not it.
    let extended_Z = domain
        .elements()
        .enumerate()
        .map(|(ix, w)| (w * gen.cofactor).pow(vec![ix as u64]))
        .collect::<Vec<_>>();

    println!("ckpoint 5");

    let q_B_evals = (0..n).map(|i| (extended_b[i] * (extended_f[i] + beta) - F::one()) / &extended_Z[i]).collect::<Vec<_>>();
    // Instead of this we can actually do an MSM with the committed Lagrangian bases
    let q_B = domain.ifft(&q_B_evals);
    println!("ckpoint 6");

    let q_B_commit = commit_g1(&q_B, &gen.srs);
    let N: usize = t.len();
    let mut P_poly = vec![F::zero(); N - 1 - (n - 2)];
    P_poly.extend(b_0.clone());

    let p_commit = commit_g1(&P_poly, &gen.srs);

    transcript.b0 = Some(DensePolynomial { coeffs: b_0 });
    transcript.q_B = Some(DensePolynomial { coeffs: q_B });
    transcript.q_B_evals = Some(q_B_evals);
    Round2Message { 
        q_a: q_commit,
        a: a_commit,
        b_0_commit,
        p_commit,
    }
}

fn round_2_verify(round_1_msg: &Round1Message, round_2_msg: &Round2Message, transcript: &Transcript, gen: &GenOutput) {
    // Perform the first check
    let l_pairing = Bls12_381::pairing(round_2_msg.a, &gen.t_commit);
    let r_pairing = Bls12_381::pairing(round_2_msg.q_a, &gen.z_commit)
        + Bls12_381::pairing(round_1_msg.m - round_2_msg.a * transcript.beta.clone().unwrap(), G2::generator());
    assert_eq!(l_pairing, r_pairing);

    // Perform the second check
    // let l2_pairing = Bls12_381::pairing();
}

fn round_3(f: &Vec<F>, t: &Vec<F>, transcript: &mut Transcript, gen: &GenOutput) {
    let n: usize = f.len();
    let beta = transcript.beta.clone().unwrap();
    let gamma = transcript.gamma.clone().unwrap();
    let eta = transcript.eta.clone().unwrap();
    let q_B = transcript.q_B.clone().unwrap();
    let q_B_evals = transcript.q_B_evals.clone().unwrap();

    let domain = GeneralEvaluationDomain::<F>::new(f.len()).unwrap();
    let b0 = transcript.b0.clone().unwrap();
    let f_poly = DensePolynomial { coeffs: domain.ifft(f) };

    let f_eval = f_poly.evaluate(&gamma);
    let b0_eval = b0.evaluate(&gamma);
    
    let a_0 = F::one();
    let q_B_eval = q_B.evaluate(&gamma);

    let v = b0_eval + eta * f_eval + eta * eta * q_B_eval;

    let b0_evals = domain.ifft(&b0);

    let roots = domain.elements();
    let h_evals = 
        domain.elements().enumerate().map(|(i, el)| (b0_evals[i] + eta * f[i] + eta * eta * q_B_evals[i]) / (el - eta)).collect::<Vec<_>>();
    let h_poly = domain.ifft(&h_evals);
    let h_commit = commit_g1(&h_poly, &gen.srs);

    let mut a_0 = G1::zero();
    let m = transcript.m.clone().unwrap();
    for (ix, m_el) in m.iter() {
        a_0 += gen.Li_shifted_commits[*ix as usize] * &(m_el / &(t[*ix as usize] + beta));
    }
}

fn random_F() -> F {
    let mut rng = rand::thread_rng();
    F::rand(&mut rng)
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
    round_1(&f_vec, &t_vec, &mut transcript, &gen);
    // round_2();
    // round_3();
}

#[cfg(test)]
mod tests {
    use std::{iter::Map, collections::HashMap};
    use ark_bls12_381::{G1Projective as G1, G2Projective as G2, Fr as F, G1Affine, G2Affine};
    use ark_poly::{GeneralEvaluationDomain, EvaluationDomain, univariate::DensePolynomial, DenseUVPolynomial};
    use crate::{setup, Transcript, round_1, round_2, round_2_verify, GenOutput, random_F};
    use ark_std::{Zero, One};
    use ark_poly::Polynomial;

    fn initialize_test(f: &Vec<F>, t: &Vec<F>) -> (Transcript, GenOutput) {
        let N = t.len();
        let gen = setup(N as u64, &t);
        let mut transcript = Transcript::new();
        (transcript, gen)
    }

    #[test]
    fn test_setup() {
        let convert_ff = |x: Vec<u64>| x.into_iter().map(|x| F::from(x)).collect::<Vec<_>>();
        let f_vec = convert_ff(vec![1, 2, 2, 3, 3, 3, 4, 4]);
        let t_vec = convert_ff(vec![1, 2, 3, 4, 5, 6, 7, 8]);
        let (mut transcript, gen) = initialize_test(&f_vec, &t_vec);

        // test lagrange correctness
        let domain = GeneralEvaluationDomain::<F>::new(f_vec.len()).unwrap();
        let t_poly = DensePolynomial::from_coefficients_vec(domain.ifft(&t_vec));
        assert_eq!(gen.Lis[0].evaluate(&F::one()), F::one());
        assert_eq!(gen.Lis[1].evaluate(&domain.group_gen()), F::one());

        // test cached quotient correctness
        for (ix, qi) in gen.qis.iter().enumerate() {
            println!("first one");
            assert_eq!(qi.mul_by_vanishing_poly(domain) + &gen.Lis[ix] * t_vec[ix], &gen.Lis[ix] * &t_poly);
        }
    }

    #[test]
    fn test_round_1() {
        let convert_ff = |x: Vec<u64>| x.into_iter().map(|x| F::from(x)).collect::<Vec<_>>();
        let f_vec = convert_ff(vec![1, 2, 2, 3, 3, 3, 4, 4]);
        let t_vec = convert_ff(vec![1, 2, 3, 4, 5, 6, 7, 8]);
        let (mut transcript, gen) = initialize_test(&f_vec, &t_vec);

        round_1(&f_vec, &t_vec, &mut transcript, &gen);

        let m = transcript.m.unwrap();
        let m_map = m.into_iter().collect::<HashMap<_, _>>();
        
        // Check m
        assert_eq!(m_map[&0], F::one());
        assert_eq!(m_map[&1], F::from(2));
        assert_eq!(m_map[&2], F::from(3));
        assert_eq!(m_map[&3], F::from(2));
    }

    #[test]
    fn test_round_2() {
        let convert_ff = |x: Vec<u64>| x.into_iter().map(|x| F::from(x)).collect::<Vec<_>>();
        let f_vec = convert_ff(vec![1, 2, 2, 3, 3, 3, 4, 4]);
        let t_vec = convert_ff(vec![1, 2, 3, 4, 5, 6, 7, 8]);
        let (mut transcript, gen) = initialize_test(&f_vec, &t_vec);
        let round_1_msg = round_1(&f_vec, &t_vec, &mut transcript, &gen);
        transcript.beta = Some(random_F());
        let round_2_msg = round_2(&f_vec, &t_vec, &mut transcript, &gen);
        round_2_verify(&round_1_msg, &round_2_msg, &transcript, &gen);

        let N = t_vec.len();
        let n = f_vec.len();
        let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();

        // 
    }
}