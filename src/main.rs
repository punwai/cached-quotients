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
    let coeffs = domain.ifft(evals)
        .into_iter()
        .enumerate()
        .map(|(i, x)| x * &cofactor.pow(vec![i as u64]))
        .collect::<Vec<_>>();
    domain.fft(&coeffs)
}

fn extended_bases_to_coeffs(n: usize, evals: &[F], cofactor: &F) -> Vec<F> {
    let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let inv_offset = F::one() / cofactor;
    domain.ifft(&evals)
        .iter()
        .enumerate()
        .map(|(i, x)| x * &inv_offset.pow(vec![i as u64]))
        .collect::<Vec<_>>()
}

fn setup(N: u64, t: &Vec<F>) -> GenOutput {
    let srs = TrustedSetupParams::new(N);
    let domain = GeneralEvaluationDomain::<F>::new(N as usize).unwrap();

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
        Li_constants.push(L_i[0]);
        Li_commits.push(commit_g1(&L_i, &srs));
        Li_shifted_commits.push(commit_g1(&L_i[1..(N as usize)], &srs)); // Compute Q_i(x)
        Lis.push(DensePolynomial { coeffs: L_i } );
    }
    
    // Scale each of the K_i through scalar multiplication
    let cofactor = F::from(123456);
    let t_shifted = extend_lagrange_basis(N as usize, &t, &cofactor);


    let w = domain.group_gen();
    let mut w_ptr = F::one();
    let mut committed_quotients = vec![];
    let mut qis = vec![];

    for i in 0..(N as usize) {
        let Z_V = w_ptr / &F::from(N);
        let mut w_inner_ptr = F::one();
        let mut q_evals = vec![];

        for j in 0..t_shifted.len() {
            let eval = ((t_shifted[j] - t[i]) / (w_inner_ptr * cofactor - w_ptr)) * Z_V;
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
    f_poly: Option<DensePolynomial<F>>,
    // SPARSE LAGRANGIAN (index, value)
    m: Option<Vec<(u64, F)>>,
    b0: Option<DensePolynomial<F>>,
    // q_A: Option<DensePolynomial<F>>,
    q_B: Option<DensePolynomial<F>>,
    h: Option<DensePolynomial<F>>,
    B: Option<DensePolynomial<F>>,
    beta: Option<F>,
    gamma: Option<F>,
    eta: Option<F>,
}

impl Transcript {
    fn new() -> Self {
        Self {
            f_poly: None,
            m: None,
            b0: None,
            B: None,
            beta: None,
            gamma: None,
            h: None,
            eta: None,
            q_B: None,
        }
    }
}
struct Round1Message {
    m: G1,
    cm: G1,
}

struct Round2Message {
    a: G1,
    q_a: G1,
    b_0_commit: G1,
    p_commit: G1,
    q_B_commit: G1
}

struct Round3Message {
    a_0: F,
    b_0_commit: F,
    f_commit: F,
    quot_commit: G1,
    a_0_commit: G1
}

fn round_1(f: &Vec<F>, t: &Vec<F>, transcript: &mut Transcript, gen: &GenOutput) -> Round1Message {
    /* 1 */
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

    /* 2 */
    let domain = GeneralEvaluationDomain::<F>::new(f.len()).unwrap();
    let f_poly = domain.ifft(&f);
    transcript.f_poly = Some(DensePolynomial::from_coefficients_vec(f_poly.clone()));
    let f_commit = commit_g1(&f_poly, &gen.srs);
    Round1Message { m: m_commit, cm: f_commit }
}

fn round_2(f: &Vec<F>, t: &Vec<F>, transcript: &mut Transcript, gen: &GenOutput) -> Round2Message {
    /* 1-. */
    let beta = transcript.beta.clone().unwrap();
    /* 2- */
    let m = transcript.m.clone().unwrap();
    let mut a_commit = G1::zero();
    for (ix, m_el) in m.iter() {
        a_commit += &(gen.Li_commits[*ix as usize] * (m_el / &(t[*ix as usize] + beta)));
    }
    /* 3 */
    /* 4 */
    let mut q_commit = G1::zero();
    for (ix, m_el) in m.iter() {
        let a_i = (m_el) / &(t[*ix as usize] + beta);
        q_commit += &(gen.qi_commits[*ix as usize] * a_i);
    }
    /* 5 */
    let domain = GeneralEvaluationDomain::<F>::new(f.len()).unwrap();
    let b_evals = f.iter().map(|f_el| F::one() / (f_el + &beta)).collect::<Vec<_>>();
    /* 6 */
    /* 7 */
    let b_poly = domain.ifft(&b_evals);
    let b_0 = b_poly.clone().into_iter().skip(1).collect::<Vec<_>>();
    let b_0_commit = commit_g1(&b_0, &gen.srs);
    /* 8 */
    let n = f.len();
    let extended_b = extend_lagrange_basis(n, &b_evals, &gen.cofactor);
    let extended_f = extend_lagrange_basis(n, &f, &gen.cofactor);
    let extended_Z = domain
        .elements()
        .map(|w| (w * gen.cofactor).pow(vec![n as u64]) - F::one())
        .collect::<Vec<_>>();
    let q_B_evals = (0..extended_b.len()).map(|i| (extended_b[i] * (extended_f[i] + beta) - F::one()) / &extended_Z[i]).collect::<Vec<_>>();
    let q_B = extended_bases_to_coeffs(n, &q_B_evals, &gen.cofactor);

    /* 9 */
    let q_B_commit = commit_g1(&q_B, &gen.srs);

    /* 10 */
    let N: usize = t.len();
    let mut P_poly = vec![F::zero(); N - 1 - (n - 2)];
    P_poly.extend(b_0.clone());
    let p_commit = commit_g1(&P_poly, &gen.srs);

    transcript.b0 = Some(DensePolynomial { coeffs: b_0 });
    transcript.q_B = Some(DensePolynomial::from_coefficients_vec(q_B));
    transcript.B = Some(DensePolynomial { coeffs: b_poly });
    Round2Message { 
        q_a: q_commit,
        a: a_commit,
        b_0_commit,
        p_commit,
        q_B_commit
    }
}

fn round_3(f: &Vec<F>, t: &Vec<F>, transcript: &mut Transcript, gen: &GenOutput) -> Round3Message{
    /* 0 */
    let n: usize = f.len();
    let N: usize = t.len();
    let domain = GeneralEvaluationDomain::<F>::new(f.len()).unwrap();
    let beta = transcript.beta.clone().unwrap();
    let gamma = transcript.gamma.clone().unwrap();
    let eta = transcript.eta.clone().unwrap();
    let q_B = transcript.q_B.clone().unwrap();
    let b0 = transcript.b0.clone().unwrap();
    let B = transcript.B.clone().unwrap();

    let f_poly = DensePolynomial { coeffs: domain.ifft(f) };
    /* 2 */
    let f_eval = f_poly.evaluate(&gamma);
    let b0_eval = b0.evaluate(&gamma);
    /* 3 */
    let m = transcript.m.clone().unwrap();
    let mut a_0 = F::zero();
    for (ix, m_el) in m.iter() {
        a_0 += m_el / &(t[*ix as usize] + beta) * &gen.Li_constants[*ix as usize];
    }
    /* 4 */
    let b_0 = (a_0 * F::from(N as u64)) / F::from(n as u64);
    /* 5 */
    let b_gamma = b_0 + b0_eval * gamma;
    assert!(B.evaluate(&gamma) == b_gamma);

    let q_B_gamma = (b_gamma * (f_eval + beta) - F::one()) / (gamma.pow(vec![n as u64]) - F::one());
    assert!(q_B.evaluate(&gamma) == q_B_gamma);

    /* 6a */
    let v = b0_eval + eta * f_eval + eta * eta * q_B_gamma;

    /* 6b */
    let b0_evals = domain.fft(&b0);
    let q_B_evals = domain.fft(&q_B);

    let h_evals = 
        domain.elements().enumerate().map(|(i, el)| (b0_evals[i] + eta * f[i] + eta * eta * q_B_evals[i] - v) / (el - gamma)).collect::<Vec<_>>();
        
    println!("First domain element {:?}", domain.elements().next().unwrap());
    let h_poly = domain.ifft(&h_evals);

    transcript.h = Some(DensePolynomial::from_coefficients_vec(h_poly.clone()));
    let h_commit = commit_g1(&h_poly, &gen.srs);

    let mut a_0_commit = G1::zero();
    let m = transcript.m.clone().unwrap();
    for (ix, m_el) in m.iter() {
        a_0_commit += gen.Li_shifted_commits[*ix as usize] * &(m_el / &(t[*ix as usize] + beta));
    }

    Round3Message { a_0, b_0_commit: b0_eval, f_commit: f_eval, quot_commit: h_commit, a_0_commit }
}

fn round_2_verify(n: u64, round_1_msg: &Round1Message, round_2_msg: &Round2Message, transcript: &Transcript, gen: &GenOutput) {
    // Perform the first check
    let l_pairing = Bls12_381::pairing(round_2_msg.a, &gen.t_commit);
    let r_pairing = Bls12_381::pairing(round_2_msg.q_a, &gen.z_commit)
        + Bls12_381::pairing(round_1_msg.m - round_2_msg.a * transcript.beta.clone().unwrap(), G2::generator());
    assert_eq!(l_pairing, r_pairing);

    // Perform the second check
    let N = gen.N;
    let l2_pairing = Bls12_381::pairing(
        round_2_msg.b_0_commit, &gen.srs.g2s[(N - 1 - (n - 2)) as usize]
    );
    let r2_pairing = Bls12_381::pairing(
        round_2_msg.p_commit, G2::generator()
    );
    assert_eq!(l2_pairing, r2_pairing);
}

fn round_3_verify(n: u64, round_1_msg: &Round1Message, round_2_msg: &Round2Message, round_3_msg: &Round3Message, transcript: &Transcript, gen: &GenOutput) {
    /* 0 */
    let gamma = transcript.gamma.clone().unwrap();
    let eta = transcript.eta.clone().unwrap();
    let beta = transcript.beta.clone().unwrap();
    let h = transcript.h.clone().unwrap();
    let q_B = transcript.q_B.clone().unwrap();
    let B0 = transcript.b0.clone().unwrap();
    let f_poly = transcript.f_poly.clone().unwrap();
    let domain = GeneralEvaluationDomain::<F>::new(n as usize).unwrap();

    /* 4 */
    let b0 = F::from(gen.N) * round_3_msg.a_0 / F::from(n);

    /* 5 */
    let b_gamma = round_3_msg.b_0_commit * gamma + b0;
    let Z_H_gamma = gamma.pow(vec![n as u64]) - F::one();
    let Q_b_gamma = (b_gamma * (round_3_msg.f_commit + beta) - F::one()) / Z_H_gamma;

    /* 6 */
    let v = round_3_msg.b_0_commit + eta * round_3_msg.f_commit + eta * eta * Q_b_gamma;
    let c = &round_2_msg.b_0_commit + round_1_msg.cm * eta + round_2_msg.q_B_commit * eta * eta;

    assert_eq!(
        Bls12_381::pairing(c - G1::generator() * v + round_3_msg.quot_commit * gamma, G2::generator()),
        Bls12_381::pairing(round_3_msg.quot_commit, gen.srs.g2s[1])
    );

    assert_eq!(
        Bls12_381::pairing(round_2_msg.a - G1::generator() * round_3_msg.a_0, G2::generator()),
        Bls12_381::pairing(round_3_msg.a_0_commit, gen.srs.g2s[1])
    )
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
    use std::{ops::{Mul, Sub, Neg}};
    use ark_poly::{GeneralEvaluationDomain, EvaluationDomain, univariate::DensePolynomial, DenseUVPolynomial};
    use crate::{setup, Transcript, round_1, round_2, round_2_verify, GenOutput, random_F, round_3, round_3_verify};
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

    fn poly(v: Vec<F>) -> DensePolynomial<F> {
        DensePolynomial { coeffs: v }
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

        let n = f_vec.len() as u64;
        round_2_verify(n, &round_1_msg, &round_2_msg, &transcript, &gen);

        // Check that Q_b is computed correctly
        let Q_b = transcript.q_B.clone().unwrap();
        let B = transcript.B.clone().unwrap();
        let B0 = transcript.b0.clone().unwrap();
        let beta = transcript.beta.clone().unwrap();
        let domain = GeneralEvaluationDomain::<F>::new(n as usize).unwrap();
        let f_poly = poly(domain.ifft(&f_vec));
        // B is computed correctly 
        for (ix, w) in domain.elements().enumerate() {
            assert_eq!(B.evaluate(&w), F::one() / (f_vec[ix] + beta))
        }
        // B0 is computed correctly
        assert_eq!(B0, &(&B - &poly(vec![B.evaluate(&F::zero())])) / &DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]));
        // Q_b is computed correctly
        assert_eq!(
            &Q_b * &DensePolynomial::from(domain.vanishing_polynomial()),
            &(&B * &(&f_poly + &DensePolynomial::from_coefficients_vec(vec![beta])))
                - &DensePolynomial::from_coefficients_vec(vec![F::one()])
        );
    }

    #[test]
    fn test_round_3() {
        let convert_ff = |x: Vec<u64>| x.into_iter().map(|x| F::from(x)).collect::<Vec<_>>();
        let f_vec = convert_ff(vec![1, 2, 3, 4, 5, 6, 7, 8]);
        let t_vec = convert_ff(vec![1, 2, 3, 4, 5, 6, 7, 8]);
        let (mut transcript, gen) = initialize_test(&f_vec, &t_vec);
        let round_1_msg = round_1(&f_vec, &t_vec, &mut transcript, &gen);
        transcript.beta = Some(random_F());
        let round_2_msg = round_2(&f_vec, &t_vec, &mut transcript, &gen);
        transcript.eta = Some(random_F());
        transcript.gamma = Some(random_F());
        let round_3_msg = round_3(&f_vec, &t_vec, &mut transcript, &gen);

        round_3_verify(f_vec.len() as u64, &round_1_msg, &round_2_msg, &round_3_msg, &transcript, &gen);
    }
}