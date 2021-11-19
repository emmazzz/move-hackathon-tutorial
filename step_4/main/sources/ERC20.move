/// This module defines the following three methods in ERC 20 standard:
/// function totalSupply() public view returns (uint256)
/// function balanceOf(address _owner) public view returns (uint256 balance)
/// function transfer(address _to, uint256 _value) public returns (bool success)
module Sender::ERC20 {
    use Std::Signer;

    const ENOT_MODULE_OWNER: u64 = 0;
    const MODULE_OWNER: address = @Sender;
    const EINSUFFICIENT_BALANCE: u64 = 1;

    struct TotalSupply has key {
        supply: u64
    }

    struct Coin has store {
        value: u64
    }

    struct Balance has key {
        coin: Coin
    }

    fun withdraw(addr: address, amount: u64) : Coin acquires Balance {
        let balance = balance_of(addr);
        assert!(balance >= amount, EINSUFFICIENT_BALANCE);
        let balance_ref = &mut borrow_global_mut<Balance>(addr).coin.value;
        *balance_ref = balance - amount;
        Coin { value: amount }
    }

    fun deposit(addr: address, check: Coin) acquires Balance{
        let balance = balance_of(addr);
        let balance_ref = &mut borrow_global_mut<Balance>(addr).coin.value;
        let Coin { value } = check;
        *balance_ref = balance + value;
    }

    public fun total_supply(): u64 acquires TotalSupply {
        borrow_global<TotalSupply>(MODULE_OWNER).supply
    }

    public fun balance_of(owner: address): u64 acquires Balance {
        borrow_global<Balance>(owner).coin.value
    }

    public(script) fun initialize_erc20(module_owner: signer) {
        assert!(Signer::address_of(&module_owner) == MODULE_OWNER, ENOT_MODULE_OWNER);
        move_to(&module_owner, TotalSupply { supply: 0 });
    }

    public(script) fun transfer(from: signer, to: address, amount: u64) acquires Balance {
        let check = withdraw(Signer::address_of(&from), amount);
        deposit(to, check);
    }

    public(script) fun mint_token(owner: signer, amount: u64) acquires Balance {
        deposit(Signer::address_of(&owner), Coin { value: amount });
        // TODO: increment total supply
    }

}

