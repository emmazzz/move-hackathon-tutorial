/// This module defines a minimal Coin and Balance.
module NamedAddr::BasicCoin {
    use Std::Errors;
    use Std::Signer;

    /// Address of the owner of this module
    const MODULE_OWNER: address = @NamedAddr;

    /// Error codes
    const ENOT_MODULE_OWNER: u64 = 0;
    const EINSUFFICIENT_BALANCE: u64 = 1;
    const EALREADY_HAS_BALANCE: u64 = 2;

    struct Coin has store {
        value: u64
    }

    /// Struct representing the balance of each address.
    struct Balance has key {
        coin: Coin
    }

    /// Initialize this module.
    public(script) fun initialize(module_owner: signer, total_supply: u64) acquires Balance {
        // Only the owner of the module can initialize this module
        assert!(Signer::address_of(&module_owner) == MODULE_OWNER, Errors::requires_address(ENOT_MODULE_OWNER));

        // Publish an empty balance under the module owner's address
        publish_balance(&module_owner);
        // Deposit `total_value` amount of tokens to module owner's balance
        deposit(MODULE_OWNER, Coin { value: total_supply });
    }

    /// Publish an empty balance resource under `account`'s address.
    fun publish_balance(account: &signer) {
        let empty_coin = Coin { value: 0 };
        // TODO: Remove this ! and have them fix it
        assert!(!exists<Balance>(Signer::address_of(account)), Errors::already_published(EALREADY_HAS_BALANCE));
        move_to(account, Balance { coin:  empty_coin });
    }

    /// Returns the balance of `owner`.
    public fun balance_of(owner: address): u64 acquires Balance {
        borrow_global<Balance>(owner).coin.value
    }

    /// Transfers `amount` of tokens from `from` to `to`.
    public(script) fun transfer(from: signer, to: address, amount: u64) acquires Balance {
        let check = withdraw(Signer::address_of(&from), amount);
        deposit(to, check);
    }

    /// Withdraw `amount` number of tokens from the balance under `addr`.
    fun withdraw(addr: address, amount: u64) : Coin acquires Balance {
        let balance = balance_of(addr);
        // balance must be greater than the withdraw amount
        assert!(balance >= amount, Errors::limit_exceeded(EINSUFFICIENT_BALANCE));
        let balance_ref = &mut borrow_global_mut<Balance>(addr).coin.value;
        *balance_ref = balance - amount;
        Coin { value: amount }
    }

    /// Deposit `amount` number of tokens to the balance under `addr`.
    fun deposit(addr: address, check: Coin) acquires Balance{
        let balance = balance_of(addr);
        let balance_ref = &mut borrow_global_mut<Balance>(addr).coin.value;
        let Coin { value } = check;
        *balance_ref = balance + value;
    }

    #[test(account = @0x1)]
    #[expected_failure] // This test should abort
    public(script) fun init_non_owner(account: signer) acquires Balance {
        // Make sure the address we've chosen doesn't match the module
        // owner address
        assert!(Signer::address_of(&account) != MODULE_OWNER, 0);
        initialize(account, 10);
    }

    #[test(account = @NamedAddr)]
    public(script) fun init_check_balance(account: signer) acquires Balance {
        // Make sure the address we've chosen doesn't match the module
        // owner address
        let total_supply = 1000;
        let addr = Signer::address_of(&account);
        initialize(account, total_supply);
        assert!(balance_of(addr) == total_supply, 0);
    }

    #[test(account = @0x1)]
    fun publish_balance_has_zero(account: signer) acquires Balance {
        let addr = Signer::address_of(&account);
        publish_balance(&account);
        assert!(balance_of(addr) == 0, 0);
    }

    #[test(account = @0x1)]
    #[expected_failure(abort_code = 518)] // Can specify an abort code
    fun publish_balance_already_exists(account: signer) {
        publish_balance(&account);
        publish_balance(&account);
    }

    #[test]
    #[expected_failure]
    fun balance_of_dne() acquires Balance {
        balance_of(@0x1);
    }

    #[test]
    #[expected_failure]
    fun withdraw_dne() acquires Balance {
        // Need to unpack the coin since `Coin` is a resource
        Coin { value: _ } = withdraw(@0x1, 0);
    }

    #[test(account = @0x1)]
    #[expected_failure] // This test should fail
    fun withdraw_too_much(account: signer) acquires Balance {
        let addr = Signer::address_of(&account);
        publish_balance(&account);
        Coin { value: _ } = withdraw(addr, 1);
    }

    #[test(account = @NamedAddr)]
    public(script) fun can_withdraw_amount(account: signer) acquires Balance {
        let total_supply = 1000;
        let addr = Signer::address_of(&account);
        initialize(account, total_supply);
        let Coin { value } = withdraw(addr, total_supply);
        assert!(value == total_supply, 0);
    }
}
