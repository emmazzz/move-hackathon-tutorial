module NamedAddr::BasicCoin {
    struct Coin has store {
        value: u64
    }

    struct Balance has key {
        coin: Coin
    }

    public fun balance_of(owner: address): u64 acquires Balance;

    public(script) fun transfer(from: signer, to: address, amount: u64) acquires Balance;
}

