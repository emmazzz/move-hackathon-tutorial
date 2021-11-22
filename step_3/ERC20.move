module Sender::ERC20 {
    struct TotalSupply has key {
        supply: u64
    }

    struct Coin has store {
        value: u64
    }

    struct Balance has key {
        coin: Coin
    }

    public fun total_supply(): u64 acquires TotalSupply;

    public fun balance_of(owner: address): u64 acquires Balance;

    public(script) fun transfer(from: signer, to: address, amount: u64) acquires Balance;
}

