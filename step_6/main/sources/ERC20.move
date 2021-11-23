/// This module defines a minimal and generic ERC 20 token.
module Sender::ERC20 {
    use Std::Signer;

    /// Error codes
    const ENOT_MODULE_OWNER: u64 = 0;
    const EINSUFFICIENT_BALANCE: u64 = 1;
    const EALREADY_INITIALIZED: u64 = 2;

    struct Coin<phantom CoinType> has store {
        value: u64
    }

    struct Balance<phantom CoinType> has key {
        coin: Coin<CoinType>
    }

    fun withdraw<CoinType>(addr: address, amount: u64) : Coin<CoinType> acquires Balance {
        let balance = balance_of<CoinType>(addr);
        assert!(balance >= amount, EINSUFFICIENT_BALANCE);
        let balance_ref = &mut borrow_global_mut<Balance<CoinType>>(addr).coin.value;
        *balance_ref = balance - amount;
        Coin<CoinType> { value: amount }
    }

    fun deposit<CoinType>(addr: address, check: Coin<CoinType>) acquires Balance{
        let balance = balance_of<CoinType>(addr);
        let balance_ref = &mut borrow_global_mut<Balance<CoinType>>(addr).coin.value;
        let Coin { value } = check;
        *balance_ref = balance + value;
    }

    public fun balance_of<CoinType>(owner: address): u64 acquires Balance {
        borrow_global<Balance<CoinType>>(owner).coin.value
    }

    public(script) fun transfer<CoinType>(from: signer, to: address, amount: u64) acquires Balance {
        let check = withdraw<CoinType>(Signer::address_of(&from), amount);
        deposit<CoinType>(to, check);
    }


    public fun initialize_erc20<CoinType>(module_owner: &signer, total_supply: u64) acquires Balance {
        // Publish an empty balance under the module owner's address
        publish_balance<CoinType>(module_owner);
        // Deposit `total_value` amount of tokens to module owner's balance
        deposit(Signer::address_of(module_owner), Coin<CoinType> { value: total_supply });
    }

    public fun publish_balance<CoinType>(account: &signer) {
        let empty_coin = Coin<CoinType> { value: 0 };
        move_to(account, Balance<CoinType> { coin:  empty_coin });
    }
}


//module EmmaCoin {
//    const EMMA_ADDR: address = 0x42;
//    struct EmmaCoin {}
//    public(script) fun initialize(emma: signer) {
//        assert(address_of(&emma) == EMMA_ADDR);
//        initialize_erc20<EmmaCoin>(&emma, 10000, EmmaCoin {});
//    }
//}

