/// This module defines a minimal ERC 20 token.
module Sender::ERC20 {
    use Std::Errors;
    use Std::Signer;

    /// Address of the owner of this module
    const MODULE_OWNER: address = @Sender;

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

    /// Struct representing the total supply of tokens,
    /// stored under module owner's address
    struct TotalSupply has key {
        supply: u64
    }

    /// Initialize this module.
    public(script) fun initialize_erc20(module_owner: signer, total_supply: u64) {
        // Only the owner of the module can initialize this module
        assert!(Signer::address_of(&module_owner) == MODULE_OWNER, ENOT_MODULE_OWNER);

        // Publish an empty balance under the module owner's address
        publish_balance(&module_owner);
        // Deposit `total_value` amount of tokens to module owner's balance
        deposit(MODULE_OWNER, Coin { value: total_supply });

        // TODO: publish TotalSupply resource under the module owner's address using `move_to`
    }

    /// Publish an empty balance resource under `account`'s address.
    fun publish_balance(account: &signer) {
        let empty_coin = Coin { value: 0 };
        assert!(exists<Balance>(Signer::address_of(account)), Errors::already_published(EALREADY_HAS_BALANCE));
        move_to(account, Balance { coin:  empty_coin });
    }

    /// Returns the balance of `owner`.
    public fun balance_of(owner: address): u64 acquires Balance {
        borrow_global<Balance>(owner).coin.value
    }

    /// Returns the total supply of tokens. This should always return the same number since we
    /// don't have any way to mint or burn coins right now.
    public fun total_supply(): u64 acquires TotalSupply {
        borrow_global<TotalSupply>(MODULE_OWNER).supply
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
    fun deposit(_addr: address, check: Coin) {
        // TODO: follow the implementation of `withdraw` and implement me!
        let Coin { value: _amount } = check; // unpacks the check

        // Get a mutable reference of addr's balance's coin value

        // Increment the value by `amount`
    }
}

