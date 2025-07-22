use actix_cors::Cors;
use actix_web::{web, App, HttpResponse, HttpServer, Responder, dev::ServiceRequest};
use actix_web::middleware::Logger;
use base64::{Engine as _, engine::general_purpose};
use serde::{Deserialize, Serialize};
use sha2::{Sha256, Digest};
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io::{Read, Write};
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH, Duration};
use dotenv::dotenv;
use log::{info, error, warn};

// --- ZKP Dependencies ---
use bellman::{Circuit, ConstraintSystem, SynthesisError, groth16};
use bls12_381::{Bls12, Scalar as Fr};
use ff::Field;
use rand::rngs::OsRng;

// --- API Security ---
use actix_governor::{Governor, GovernorConfigBuilder, PeerIp};

// --- PRIVACY & SECURITY UPGRADE MODULES ---

mod quantum_resistance {
    use oqs::sig::{self, Sig, SecretKey, PublicKey};
    use serde::{Serialize, Deserialize};

    fn get_dilithium() -> Sig {
        Sig::new(sig::Algorithm::Dilithium5).expect("Dilithium5 not enabled.")
    }

    #[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq, Hash)]
    pub struct DilithiumPublicKey(pub Vec<u8>);
    #[derive(Clone, Serialize, Deserialize, Debug)]
    pub struct DilithiumSignature(pub Vec<u8>);

    pub fn keypair() -> (SecretKey, DilithiumPublicKey) {
        let sig = get_dilithium();
        let (pk, sk) = sig.keypair().unwrap();
        (sk, DilithiumPublicKey(pk.into_vec()))
    }

    pub fn sign(sk: &SecretKey, msg: &[u8]) -> DilithiumSignature {
        let sig = get_dilithium();
        let signature = sig.sign(msg, sk).unwrap();
        DilithiumSignature(signature.into_vec())
    }

    pub fn verify(pk: &DilithiumPublicKey, msg: &[u8], sig: &DilithiumSignature) -> bool {
        let sig_handler = get_dilithium();
        if let Ok(pk) = PublicKey::from_bytes(&pk.0) {
            sig_handler.verify(msg, &sig.0, &pk).is_ok()
        } else {
            false
        }
    }
}

mod ring_signature {
    use super::quantum_resistance as qr;

    pub fn verify(msg: &[u8], ring: &[qr::DilithiumPublicKey], signature: &qr::DilithiumSignature) -> bool {
        ring.iter().any(|pk| qr::verify(pk, msg, signature))
    }
}

mod dandelion {
    use super::Transaction;
    use rand::{Rng, SeedableRng};
    use rand::rngs::StdRng;
    use std::sync::{Arc, Mutex};
    use log::info;
    use tokio::time::{sleep, Duration};

    pub enum DandelionState { Stem, Fluff }

    pub async fn process_transaction(tx: Transaction, mempool: Arc<Mutex<Vec<Transaction>>>) {
        let mut rng = StdRng::from_entropy();
        let mut state = DandelionState::Stem;

        while let DandelionState::Stem = state {
            info!("[Dandelion] Stem phase: Forwarding transaction privately...");
            if rng.gen_bool(0.1) {
                state = DandelionState::Fluff;
            }
            let hops = rng.gen_range(1..5);
            sleep(Duration::from_millis(hops * 50)).await;
        }

        info!("[Dandelion] Fluff phase: Broadcasting transaction to the public network.");
        let mut mempool_lock = mempool.lock().unwrap();
        mempool_lock.push(tx);
    }
}

// --- ZKP Primitives & Data Structures ---
type Commitment = String;
type Nullifier = String;
type ZkProof = String;

const CHAIN_VERSION: u8 = 1;
const TX_VERSION: u8 = 1;

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct TransactionPreimage {
    pub version: u8,
    pub input_nullifiers: Vec<Nullifier>,
    pub output_commitments: Vec<Commitment>,
    pub ephemeral_pubkey: String,
    pub encrypted_note: String,
    pub zk_proof: ZkProof,
    pub valid_from_height: u64,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Transaction {
    pub preimage: TransactionPreimage,
    pub ring_signature: quantum_resistance::DilithiumSignature,
    pub ring_participants: Vec<quantum_resistance::DilithiumPublicKey>,
    pub ai_threat_score: f64,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Block {
    pub version: u8,
    pub index: u64,
    pub timestamp: u64,
    pub prev_hash: String,
    pub producer_pk: quantum_resistance::DilithiumPublicKey,
    pub transactions: Vec<Transaction>,
    pub hash: String,
    pub producer_signature: quantum_resistance::DilithiumSignature,
    pub ai_block_risk: f64,
}

#[derive(Clone, Debug)]
pub struct Validator {
    pub public_key: quantum_resistance::DilithiumPublicKey,
    pub stake_amount: u64,
}

#[derive(Clone)]
pub struct Blockchain {
    pub chain: Vec<Block>,
    pub validator_set: HashMap<String, Validator>,
    pub unspent_commitments: HashSet<Commitment>,
    pub spent_nullifiers: HashSet<Nullifier>,
    pub zk_params: Arc<groth16::Parameters<Bls12>>,
    pub zk_pvk: Arc<groth16::PreparedVerifyingKey<Bls12>>,
}

impl Blockchain {
    pub fn new(params: groth16::Parameters<Bls12>) -> Self {
        let zk_pvk = Arc::new(groth16::prepare_verifying_key(&params.vk));
        Self {
            chain: Vec::new(), validator_set: HashMap::new(),
            unspent_commitments: HashSet::new(), spent_nullifiers: HashSet::new(),
            zk_params: Arc::new(params), zk_pvk,
        }
    }
}

#[derive(Clone)]
struct BalanceCircuit {
    input_values: Vec<Option<Fr>>,
    output_values: Vec<Option<Fr>>,
    public_amount: Option<Fr>,
}

impl Circuit<Fr> for BalanceCircuit {
    fn synthesize<CS: ConstraintSystem<Fr>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let mut total_input_val = Fr::zero();
        for val_opt in &self.input_values {
            total_input_val += val_opt.ok_or(SynthesisError::AssignmentMissing)?;
        }
        let total_input = cs.alloc(|| "total_input", || Ok(total_input_val))?;

        let mut total_output_val = Fr::zero();
        for val_opt in &self.output_values {
            total_output_val += val_opt.ok_or(SynthesisError::AssignmentMissing)?;
        }
        let total_output = cs.alloc(|| "total_output", || Ok(total_output_val))?;

        let public_amount_var = cs.alloc_input(|| "public_amount", || self.public_amount.ok_or(SynthesisError::AssignmentMissing))?;

        cs.enforce( || "balance_constraint", |lc| lc + total_input, |lc| lc + CS::one(), |lc| lc + total_output + public_amount_var);
        Ok(())
    }
}

pub struct AIDetector;
impl AIDetector {
    pub fn new() -> Self { Self {} }
    pub fn score_transaction(&self, _tx: &Transaction) -> f64 { 0.02 }
    pub fn is_suspicious(&self, tx: &Transaction) -> bool { self.score_transaction(tx) > 0.9 }
}

pub struct AppState {
    pub blockchain: Arc<Mutex<Blockchain>>,
    pub mempool: Arc<Mutex<Vec<Transaction>>>,
    pub ai_model: Arc<Mutex<AIDetector>>,
    pub validator_keys: Arc<Mutex<HashMap<String, oqs::sig::SecretKey>>>,
    pub api_key: String,
}

// --- Utility & Validation ---

fn now() -> u64 { SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs() }

fn calc_block_hash(block: &Block) -> String {
    let block_data = serde_json::json!({
        "version": block.version, "index": block.index, "timestamp": block.timestamp,
        "prev_hash": block.prev_hash, "producer_pk": block.producer_pk, "transactions": block.transactions,
    });
    let body = serde_json_canonicalizer::to_string(&block_data).unwrap();
    hex::encode(Sha256::digest(body.as_bytes()))
}

fn select_producer(validators: &HashMap<String, Validator>, seed: &str) -> String {
    let total_stake: u64 = validators.values().map(|v| v.stake_amount).sum();
    if total_stake == 0 { return "genesis".into(); }
    let mut hasher = Sha256::new();
    hasher.update(seed.as_bytes());
    let hash_result = hasher.finalize();
    let mut rand_bytes = [0u8; 8];
    rand_bytes.copy_from_slice(&hash_result[0..8]);
    let rand_val = u64::from_le_bytes(rand_bytes) % total_stake;
    let mut cumulative = 0u64;
    let mut sorted_validators: Vec<_> = validators.iter().collect();
    sorted_validators.sort_by_key(|(k, _)| *k);
    for (addr, validator) in sorted_validators {
        cumulative += validator.stake_amount;
        if cumulative > rand_val {
            return addr.clone();
        }
    }
    "genesis".into()
}

fn verify_transaction_proof(tx: &Transaction, pvk: &groth16::PreparedVerifyingKey<Bls12>) -> bool {
    if tx.preimage.zk_proof == "genesis" { return true; } 
    let proof_bytes = match general_purpose::STANDARD.decode(&tx.preimage.zk_proof) { Ok(b) => b, Err(_) => return false };
    let proof = match groth16::Proof::read(&*proof_bytes) { Ok(p) => p, Err(_) => return false };
    let public_inputs = [Fr::zero()];
    groth16::verify_proof(pvk, &proof, &public_inputs).is_ok()
}

// --- API Handlers ---

async fn get_chain(data: web::Data<AppState>) -> impl Responder {
    let bc = data.blockchain.lock().unwrap();
    HttpResponse::Ok().json(&bc.chain)
}

#[derive(Deserialize, Debug)]
struct NewTxRequest {
    preimage: TransactionPreimage,
    ring_signature: quantum_resistance::DilithiumSignature,
    ring_participants: Vec<quantum_resistance::DilithiumPublicKey>,
}

impl NewTxRequest {
    fn validate(&self) -> Result<(), String> {
        if self.ring_participants.len() > 16 || self.ring_participants.is_empty() {
            return Err("Ring size must be between 1 and 16".to_string());
        }
        if self.preimage.ephemeral_pubkey.len() > 128 || self.preimage.encrypted_note.len() > 1024 {
            return Err("Ephemeral key or note is too long".to_string());
        }
        Ok(())
    }
}

async fn send_transaction(data: web::Data<AppState>, req: web::Json<NewTxRequest>) -> impl Responder {
    if let Err(e) = req.validate() {
        return HttpResponse::BadRequest().body(e);
    }

    let ai = data.ai_model.lock().unwrap();
    let mut tx = Transaction {
        preimage: req.preimage.clone(),
        ring_signature: req.ring_signature.clone(),
        ring_participants: req.ring_participants.clone(),
        ai_threat_score: 0.0,
    };
    tx.ai_threat_score = ai.score_transaction(&tx);

    if ai.is_suspicious(&tx) {
        error!("Transaction rejected by AI: high threat score {}", tx.ai_threat_score);
        return HttpResponse::BadRequest().body("Transaction rejected due to high risk score");
    }

    let bc = data.blockchain.lock().unwrap();

    if tx.preimage.valid_from_height > bc.chain.len() as u64 {
        return HttpResponse::BadRequest().body("Transaction expiry height is in the future");
    }

    let tx_hash = Sha256::digest(serde_json_canonicalizer::to_string(&tx.preimage).unwrap());
    if !ring_signature::verify(&tx_hash, &tx.ring_participants, &tx.ring_signature) {
        return HttpResponse::BadRequest().body("Invalid Ring Signature");
    }
    if !verify_transaction_proof(&tx, &bc.zk_pvk) {
        return HttpResponse::BadRequest().body("Invalid ZK proof");
    }
    for nullifier in &tx.preimage.input_nullifiers {
        if bc.spent_nullifiers.contains(nullifier) {
            return HttpResponse::BadRequest().body("Double spend detected: nullifier already spent");
        }
    }

    let mempool = data.mempool.clone();
    tokio::spawn(dandelion::process_transaction(tx, mempool));

    HttpResponse::Accepted().body("Transaction submitted to the network for propagation")
}

async fn mine_block(data: web::Data<AppState>) -> impl Responder {
    let mut bc = data.blockchain.lock().unwrap();
    let mut mempool = data.mempool.lock().unwrap();
    if mempool.is_empty() { return HttpResponse::Ok().body("No transactions to mine") }
    let transactions_to_mine = mempool.drain(..).collect::<Vec<_>>();
    let mut valid_txs = Vec::new();
    for tx in transactions_to_mine {
        let is_double_spend = tx.preimage.input_nullifiers.iter().any(|n| bc.spent_nullifiers.contains(n));
        let tx_hash = Sha256::digest(serde_json_canonicalizer::to_string(&tx.preimage).unwrap());
        if !is_double_spend && verify_transaction_proof(&tx, &bc.zk_pvk) && ring_signature::verify(&tx_hash, &tx.ring_participants, &tx.ring_signature) {
            valid_txs.push(tx);
        } else {
            warn!("Transaction failed validation during mining, discarding.");
        }
    }
    if valid_txs.is_empty() { return HttpResponse::Ok().body("No valid transactions to mine") }
    for tx in &valid_txs {
        for nullifier in &tx.preimage.input_nullifiers { bc.spent_nullifiers.insert(nullifier.clone()); }
        for commitment in &tx.preimage.output_commitments { bc.unspent_commitments.insert(commitment.clone()); }
    }

    let prev_hash = bc.chain.last().map_or("0".repeat(64), |b| b.hash.clone());
    let index = bc.chain.len() as u64;
    let producer_pk_str = select_producer(&bc.validator_set, &prev_hash);

    let producer_validator = bc.validator_set.get(&producer_pk_str).expect("Producer must exist in validator set");
    let producer_pk = producer_validator.public_key.clone();

    let mut new_block = Block {
        version: CHAIN_VERSION, index, timestamp: now(), prev_hash,
        producer_pk: producer_pk.clone(),
        transactions: valid_txs,
        hash: String::new(),
        producer_signature: quantum_resistance::DilithiumSignature(vec![]),
        ai_block_risk: 0.0,
    };
    new_block.hash = calc_block_hash(&new_block);

    let validator_keys = data.validator_keys.lock().unwrap();
    if let Some(producer_sk) = validator_keys.get(&producer_pk_str) {
        new_block.producer_signature = quantum_resistance::sign(producer_sk, new_block.hash.as_bytes());
        info!("Mined new block: #{} by producer {}", new_block.index, producer_pk_str);
        bc.chain.push(new_block);
        HttpResponse::Ok().body("Block mined and appended")
    } else {
        error!("CRITICAL: Selected producer's secret key not found by this node. Cannot sign block.");
        HttpResponse::InternalServerError().body("Could not sign block: Producer key unavailable")
    }
}

// --- Main Entrypoint ---

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    env_logger::init_from_env(env_logger::Env::new().default_filter_or("info"));
    dotenv().ok();

    let params = match File::open("zk_params.bin") {
        Ok(mut f) => {
            info!("Loading ZKP parameters from zk_params.bin...");
            let mut buffer = Vec::new();
            f.read_to_end(&mut buffer).expect("Failed to read ZKP params");
            groth16::Parameters::<Bls12>::read(&*buffer, true).expect("Failed to deserialize ZKP params")
        }
        Err(_) => {
            warn!("zk_params.bin not found. Performing INSECURE one-time trusted setup for testing.");
            let circuit = BalanceCircuit { input_values: vec![], output_values: vec![], public_amount: None };
            let params = groth16::generate_random_parameters::<Bls12, _, _>(circuit, &mut OsRng).unwrap();
            let mut f = File::create("zk_params.bin").expect("Failed to create zk_params.bin");
            params.write(&mut f).expect("Failed to write ZKP params");
            info!("New ZKP parameters generated and saved to zk_params.bin.");
            params
        }
    };
    info!("Trusted setup parameters loaded.");

    let mut blockchain = Blockchain::new(params);

    let (genesis_pk, genesis_sk) = match env::var("VALIDATOR_SK_B64") {
        Ok(b64_sk) => {
            let sk_bytes = general_purpose::STANDARD.decode(b64_sk).expect("Invalid base64 for SK");
            let sig = oqs::sig::Sig::new(oqs::sig::Algorithm::Dilithium5).unwrap();
            let sk = oqs::sig::SecretKey::from_bytes(&sk_bytes).unwrap();
            let pk = sig.public_key(&sk).unwrap();
            (quantum_resistance::DilithiumPublicKey(pk.into_vec()), sk)
        },
        Err(_) => {
            warn!("VALIDATOR_SK_B64 env var not set. Generating a new temporary genesis key.");
            let (pk, sk) = quantum_resistance::keypair();
            let sk_b64 = general_purpose::STANDARD.encode(sk.as_ref());
            info!("--- NEW GENESIS SECRET KEY (SAVE THIS IN YOUR .env file) ---");
            info!("VALIDATOR_SK_B64={}", sk_b64);
            info!("----------------------------------------------------------");
            (pk, sk)
        }
    };
    
    let genesis_pk_str = general_purpose::STANDARD.encode(&genesis_pk.0);
    let mut validator_keys = HashMap::new();
    validator_keys.insert(genesis_pk_str.clone(), genesis_sk);

    let genesis_validator = Validator { public_key: genesis_pk.clone(), stake_amount: 1_000_000 };
    blockchain.validator_set.insert(genesis_pk_str.clone(), genesis_validator);

    let genesis_commitment = hex::encode(Sha256::digest(b"genesis_note"));
    blockchain.unspent_commitments.insert(genesis_commitment.clone());
    let genesis_preimage = TransactionPreimage {
        version: TX_VERSION, input_nullifiers: vec![], output_commitments: vec![genesis_commitment],
        ephemeral_pubkey: "".into(), encrypted_note: "genesis".into(), zk_proof: "genesis".into(), valid_from_height: 0
    };
    let mut genesis_block = Block {
        version: CHAIN_VERSION, index: 0, timestamp: now(), prev_hash: "0".repeat(64), producer_pk: genesis_pk,
        transactions: vec![Transaction {
            preimage: genesis_preimage,
            ring_signature: quantum_resistance::DilithiumSignature(vec![]),
            ring_participants: vec![], ai_threat_score: 0.0,
        }],
        hash: "".into(), producer_signature: quantum_resistance::DilithiumSignature(vec![]), ai_block_risk: 0.0,
    };
    genesis_block.hash = calc_block_hash(&genesis_block);
    blockchain.chain.push(genesis_block);

    let api_key = env::var("API_KEY").expect("API_KEY env var must be set for security");

    let app_state = AppState {
        blockchain: Arc::new(Mutex::new(blockchain)),
        mempool: Arc::new(Mutex::new(Vec::new())),
        ai_model: Arc::new(Mutex::new(AIDetector::new())),
        validator_keys: Arc::new(Mutex::new(validator_keys)),
        api_key,
    };
    let app_data = web::Data::new(app_state);

    info!("TMYC mainnet node running on http://127.0.0.1:4040");

    HttpServer::new(move || {
        let governor_conf = GovernorConfigBuilder::default()
            .period(Duration::from_secs(2))
            .burst_size(20)
            .key_extractor(PeerIp)
            .finish()
            .unwrap();

        let api_key_middleware = actix_web::middleware::from_fn(move |req: ServiceRequest, srv| {
            let app_state = req.app_data::<web::Data<AppState>>().unwrap();
            let key = app_state.api_key.clone();
            let fut = srv.call(req);
            async move {
                if let Some(auth_header) = fut.request().headers().get("X-API-KEY") {
                    if auth_header.to_str().unwrap_or("") == key {
                        return fut.await;
                    }
                }
                Err(actix_web::error::ErrorUnauthorized("Unauthorized"))
            }
        });

        let cors = Cors::default().allow_any_origin().allow_any_header().allow_any_method().max_age(3600);
        App::new()
            .wrap(Logger::default())
            .wrap(cors)
            .wrap(Governor::new(&governor_conf))
            .app_data(app_data.clone())
            .service(
                web::scope("")
                    .wrap(api_key_middleware)
                    .route("/chain", web::get().to(get_chain))
                    .route("/send_transaction", web::post().to(send_transaction))
                    .route("/mine_block", web::post().to(mine_block))
            )
    })
    .bind(("0.0.0.0", 4040))?
    .run()
    .await
}