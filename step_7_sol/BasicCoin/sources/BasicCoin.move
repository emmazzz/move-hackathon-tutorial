/// This module defines a minimal and generic Coin and Balance.
module NamedAddr::BasicCoin {
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

    spec withdraw {
        let balance = global<Balance<CoinType>>(addr).coin.value;

        aborts_if !exists<Balance<CoinType>>(addr);
        aborts_if balance < amount;

        let post balance_post = global<Balance<CoinType>>(addr).coin.value;
        ensures result == Coin<CoinType> { value: amount };
        ensures balance_post == balance - amount;
    }

    fun deposit<CoinType>(addr: address, check: Coin<CoinType>) acquires Balance{
        let balance = balance_of<CoinType>(addr);
        let balance_ref = &mut borrow_global_mut<Balance<CoinType>>(addr).coin.value;
        let Coin { value } = check;
        *balance_ref = balance + value;
    }

    spec deposit {
        let balance = global<Balance<CoinType>>(addr).coin.value;
        let check_value = check.value;

        aborts_if !exists<Balance<CoinType>>(addr);
        aborts_if balance + check_value > MAX_U64;

        let post balance_post = global<Balance<CoinType>>(addr).coin.value;
        ensures balance_post == balance + check_value;
    }

    public fun balance_of<CoinType>(owner: address): u64 acquires Balance {
        borrow_global<Balance<CoinType>>(owner).coin.value
    }

    public(script) fun transfer<CoinType>(from: signer, to: address, amount: u64) acquires Balance {
        let check = withdraw<CoinType>(Signer::address_of(&from), amount);
        deposit<CoinType>(to, check);
    }

    spec transfer {
        let addr_from = Signer::address_of(from);

        let balance_from = global<Balance<CoinType>>(addr_from).coin.value;
        let balance_to = global<Balance<CoinType>>(to).coin.value;
        let post balance_from_post = global<Balance<CoinType>>(addr_from).coin.value;
        let post balance_to_post = global<Balance<CoinType>>(to).coin.value;

        aborts_if !exists<Balance<CoinType>>(addr_from);
        aborts_if !exists<Balance<CoinType>>(to);
        aborts_if balance_from < amount;
        aborts_if addr_from != to && balance_to + amount > MAX_U64;

        ensures addr_from != to ==> balance_from_post == balance_from - amount;
        ensures addr_from != to ==> balance_to_post == balance_to + amount;
        ensures addr_from == to ==> balance_from_post == balance_from;
    }

    public fun initialize<CoinType>(module_owner: &signer, total_supply: u64) acquires Balance {
        // Publish an empty balance under the module owner's address
        publish_balance<CoinType>(module_owner);
        // Deposit `total_value` amount of tokens to module owner's balance
        deposit(Signer::address_of(module_owner), Coin<CoinType> { value: total_supply });
    }

    spec initialize {
        include Schema_publish<CoinType> {account: module_owner, amount: total_supply};
    }

    public fun publish_balance<CoinType>(account: &signer) {
        let empty_coin = Coin<CoinType> { value: 0 };
        move_to(account, Balance<CoinType> { coin:  empty_coin });
    }

    spec publish_balance {
        include Schema_publish<CoinType> {account: account, amount: 0};
    }

    spec schema Schema_publish<CoinType> {
        account: signer;
        amount: u64;

        let addr = Signer::address_of(account);
        aborts_if exists<Balance<CoinType>>(addr);

        ensures exists<Balance<CoinType>>(addr);
        let post balance_post = global<Balance<CoinType>>(addr).coin.value;

        ensures balance_post == amount;
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
