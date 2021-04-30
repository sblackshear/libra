address 0x1 {
module KELP {
    use 0x1::BCS;
    use 0x1::Errors;
    use 0x1::Diem::{Self, Diem};
    use 0x1::DiemAccount::{Self, KeyRotationCapability};
    use 0x1::DiemTimestamp;
    use 0x1::Hash;
    use 0x1::Signer;
    use 0x1::Vector;
    use 0x1::XUS::XUS;

    /// Published under an account that supports KELP recovery
    struct KELP has key {
        /// Key rotation capability for the account that has enabled KELP recovery
        rotate_cap: KeyRotationCapability,
        /// Size of the commit fee
        fee1_amount: u64,
        /// Size of the reveal fee
        fee2_amount: u64,
        /// pooled fees from commit and reveal transactions
        fees: Diem<XUS>,
        /// Length of challenge period between commit and reveal
        t1: u64,
        /// Length of challenge period between reveal and claim
        t2: u64,
    }

    /// Published under an account that has performed a Commit operation to initiate recovery
    struct Commit has key, store {
        /// sha3(KELP address | nonce)
        commit: vector<u8>,
        /// Locked fee to be deposited upon reveal
        fee1: Diem<XUS>,
        /// Time when the commit occurred
        commit_time: u64,
    }

    /// Published under an account that has performed a successful Reveal operation
    struct Reveal has key, store {
        /// Time when the reveal occurred
        reveal_time: u64,
        /// Sequence number of the KELP account at the time of the reveal
        reveal_seq: u64,
    }

    const EBAD_REVEAL: u64 = 0;
    const EBAD_CHALLENGE: u64 = 1;
    const EBAD_CLAIM: u64 = 2;
    const EREVEAL_TOO_SOON: u64 = 3;
    const ECLAIM_TOO_SOON: u64 = 4;

    /// Enable KELP recovery for `account`
    public(script) fun initialize(
        account_r: &signer, fee1_amount: u64, fee2_amount: u64, t1: u64, t2: u64
    ) {
        let rotate_cap = DiemAccount::extract_key_rotation_capability(account_r);
        let fees = Diem::zero<XUS>();
        move_to(
            account_r,
            KELP { rotate_cap, fee1_amount, fee2_amount, fees, t1, t2 }
        )
    }

    /// Commit to a future claim on a KELP account
    public(script) fun commit(account_r: &signer, commit: vector<u8>, fee1: Diem<XUS>) {
        let commit_time = DiemTimestamp::now_seconds();
        move_to(account_r, Commit { commit, fee1, commit_time })
    }


    /// Reveal a previous claim on a KELP account
    public(script) fun reveal(
        account_r: &signer, address_c: address, nonce: vector<u8>, fee2: Diem<XUS>
    ) acquires Commit, KELP {
        let address_r = Signer::address_of(account_r);
        let Commit { commit, fee1, commit_time } = move_from<Commit>(address_r);
        let message = BCS::to_bytes(&address_c);
        Vector::append<u8>(&mut message, nonce);
        assert(Hash::sha3_256(message) == commit, Errors::invalid_argument(EBAD_REVEAL));

        let kelp = borrow_global_mut<KELP>(address_c);
        let reveal_time = DiemTimestamp::now_seconds();
        assert(reveal_time - commit_time > kelp.t1, Errors::limit_exceeded(EREVEAL_TOO_SOON));

        let reveal_seq = DiemAccount::sequence_number(address_c);
        move_to(account_r, Reveal { reveal_time, reveal_seq });

        // sweep the commit and reveal fees into the KELP resource
        Diem::deposit(&mut kelp.fees, fee1);
        Diem::deposit(&mut kelp.fees, fee2)
    }

    /// Finalize a claim on a KELP account
    public(script) fun claim(
        account_r: &signer, new_key: vector<u8>, address_c: address
    ): Diem<XUS> acquires Reveal, KELP {
        let address_r = Signer::address_of(account_r);
        let Reveal { reveal_time, reveal_seq } = move_from<Reveal>(address_r);
        let kelp = borrow_global_mut<KELP>(address_c);
        let claim_time = DiemTimestamp::now_seconds();
        // ensure the reveal was not invalidated by a subsequent "challenge" (i.e., a transaction sent
        // from address_c)
        assert(reveal_seq < DiemAccount::sequence_number(address_c), Errors::limit_exceeded(EBAD_CLAIM));
        // ensure the reveal happened afer the conclusion of the challenge period
        assert(claim_time - reveal_time > kelp.t2, Errors::limit_exceeded(ECLAIM_TOO_SOON));

        // successful claim. allower claimer to reclaim account by rotating key
        DiemAccount::rotate_authentication_key(&kelp.rotate_cap, new_key);

        // return fees to the claimer
        Diem::withdraw_all(&mut kelp.fees)
    }

    /// Collect all commit/reveal fees in the KELP resource under `account`. This can be called by
    /// the owner of the KELP resource at any time. Note: a transaction that calls `collect_fees`
    /// will also (implicitly) issue a challenge by incrementing `account`'s sequence number.
    public(script) fun collect_fees(account_c: &signer): Diem<XUS> acquires KELP {
        let address_c = Signer::address_of(account_c);
        let kelp = borrow_global_mut<KELP>(address_c);
        // return fees to the challenger
        Diem::withdraw_all(&mut kelp.fees)
    }
}
}
