
import { Serializer, Deserializer } from '../serde/mod.ts';
import { BcsSerializer, BcsDeserializer } from '../bcs/mod.ts';
import { Optional, Seq, Tuple, ListTuple, unit, bool, int8, int16, int32, int64, int128, uint8, uint16, uint32, uint64, uint128, float32, float64, char, str, bytes } from '../serde/mod.ts';

import * as DiemTypes from '../diemTypes/mod.ts';

/**
 * Structured representation of a call into a known Move script.
 */
export abstract class ScriptCall {
}


export class ScriptCallVariantSetMessage extends ScriptCall {

constructor (public message: bytes) {
  super();
}

}
/**
 * Structured representation of a call into a known Move script function.
 */
export abstract class ScriptFunctionCall {
}


export class ScriptFunctionCallVariantInitializeErc20 extends ScriptFunctionCall {

constructor (public total_supply: uint64) {
  super();
}

}

export class ScriptFunctionCallVariantSetMessage extends ScriptFunctionCall {

constructor (public message: bytes) {
  super();
}

}

export class ScriptFunctionCallVariantTransfer extends ScriptFunctionCall {

constructor (public to: DiemTypes.AccountAddress, public amount: uint64) {
  super();
}

}

export interface TypeTagDef {
  type: Types;
  arrayType?: TypeTagDef;
  name?: string;
  moduleName?: string;
  address?: string;
  typeParams?: TypeTagDef[];
}

export interface ArgDef {
  readonly name: string;
  readonly type: TypeTagDef;
  readonly choices?: string[];
  readonly mandatory?: boolean;
}

export interface ScriptDef {
  readonly stdlibEncodeFunction: (...args: any[]) => DiemTypes.Script;
  readonly stdlibDecodeFunction: (script: DiemTypes.Script) => ScriptCall;
  readonly codeName: string;
  readonly description: string;
  readonly typeArgs: string[];
  readonly args: ArgDef[];
}

export interface ScriptFunctionDef {
  readonly stdlibEncodeFunction: (...args: any[]) => DiemTypes.TransactionPayload;
  readonly description: string;
  readonly typeArgs: string[];
  readonly args: ArgDef[];
}

export enum Types {
  Boolean,
  U8,
  U64,
  U128,
  Address,
  Array,
  Struct
}


export class Stdlib {
  private static fromHexString(hexString: string): Uint8Array { return new Uint8Array(hexString.match(/.{1,2}/g)!.map((byte) => parseInt(byte, 16)));}

  /**

   */
  static encodeSetMessageScript(message: Uint8Array): DiemTypes.Script {
    const code = Stdlib.SET_MESSAGE_CODE;
    const tyArgs: Seq<DiemTypes.TypeTag> = [];
    const args: Seq<DiemTypes.TransactionArgument> = [new DiemTypes.TransactionArgumentVariantU8Vector(message)];
    return new DiemTypes.Script(code, tyArgs, args);
  }

  static decodeSetMessageScript(script: DiemTypes.Script): ScriptCallVariantSetMessage {
    return new ScriptCallVariantSetMessage(
      (script.args[0] as DiemTypes.TransactionArgumentVariantU8Vector).value
    );
  }

  /**

   */
  static encodeInitializeErc20ScriptFunction(total_supply: bigint): DiemTypes.TransactionPayload {
    const tyArgs: Seq<DiemTypes.TypeTag> = [];
    var serializer = new BcsSerializer();
    serializer.serializeU64(total_supply);
    const total_supply_serialized: bytes = serializer.getBytes();
    const args: Seq<bytes> = [total_supply_serialized];
    const module_id: DiemTypes.ModuleId = new DiemTypes.ModuleId(new DiemTypes.AccountAddress([[36], [22], [58], [252], [198], [227], [59], [10], [148], [115], [133], [46], [24], [50], [127], [169]]), new DiemTypes.Identifier("ERC20"));
    const function_name: DiemTypes.Identifier = new DiemTypes.Identifier("initialize_erc20");
    const script = new DiemTypes.ScriptFunction(module_id, function_name, tyArgs, args);
    return new DiemTypes.TransactionPayloadVariantScriptFunction(script);
  }

  /**

   */
  static encodeSetMessageScriptFunction(message: Uint8Array): DiemTypes.TransactionPayload {
    const tyArgs: Seq<DiemTypes.TypeTag> = [];
    var serializer = new BcsSerializer();
    serializer.serializeBytes(message);
    const message_serialized: bytes = serializer.getBytes();
    const args: Seq<bytes> = [message_serialized];
    const module_id: DiemTypes.ModuleId = new DiemTypes.ModuleId(new DiemTypes.AccountAddress([[36], [22], [58], [252], [198], [227], [59], [10], [148], [115], [133], [46], [24], [50], [127], [169]]), new DiemTypes.Identifier("Message"));
    const function_name: DiemTypes.Identifier = new DiemTypes.Identifier("set_message");
    const script = new DiemTypes.ScriptFunction(module_id, function_name, tyArgs, args);
    return new DiemTypes.TransactionPayloadVariantScriptFunction(script);
  }

  /**

   */
  static encodeTransferScriptFunction(to: DiemTypes.AccountAddress, amount: bigint): DiemTypes.TransactionPayload {
    const tyArgs: Seq<DiemTypes.TypeTag> = [];
    var serializer = new BcsSerializer();
    to.serialize(serializer);
    const to_serialized: bytes = serializer.getBytes();
    var serializer = new BcsSerializer();
    serializer.serializeU64(amount);
    const amount_serialized: bytes = serializer.getBytes();
    const args: Seq<bytes> = [to_serialized, amount_serialized];
    const module_id: DiemTypes.ModuleId = new DiemTypes.ModuleId(new DiemTypes.AccountAddress([[36], [22], [58], [252], [198], [227], [59], [10], [148], [115], [133], [46], [24], [50], [127], [169]]), new DiemTypes.Identifier("ERC20"));
    const function_name: DiemTypes.Identifier = new DiemTypes.Identifier("transfer");
    const script = new DiemTypes.ScriptFunction(module_id, function_name, tyArgs, args);
    return new DiemTypes.TransactionPayloadVariantScriptFunction(script);
  }

  static decodeInitializeErc20ScriptFunction(script_fun: DiemTypes.TransactionPayload): ScriptFunctionCallVariantInitializeErc20 {
  if (script_fun instanceof DiemTypes.TransactionPayloadVariantScriptFunction) {
      var deserializer = new BcsDeserializer(script_fun.value.args[0]);
      const total_supply: bigint = deserializer.deserializeU64();

      return new ScriptFunctionCallVariantInitializeErc20(
        total_supply
      );
    } else {
      throw new Error("Transaction payload not a script function payload")
    }
  }

  static decodeSetMessageScriptFunction(script_fun: DiemTypes.TransactionPayload): ScriptFunctionCallVariantSetMessage {
  if (script_fun instanceof DiemTypes.TransactionPayloadVariantScriptFunction) {
      var deserializer = new BcsDeserializer(script_fun.value.args[0]);
      const message: Uint8Array = deserializer.deserializeBytes();

      return new ScriptFunctionCallVariantSetMessage(
        message
      );
    } else {
      throw new Error("Transaction payload not a script function payload")
    }
  }

  static decodeTransferScriptFunction(script_fun: DiemTypes.TransactionPayload): ScriptFunctionCallVariantTransfer {
  if (script_fun instanceof DiemTypes.TransactionPayloadVariantScriptFunction) {
      var deserializer = new BcsDeserializer(script_fun.value.args[0]);
      const to: DiemTypes.AccountAddress = DiemTypes.AccountAddress.deserialize(deserializer);

      var deserializer = new BcsDeserializer(script_fun.value.args[1]);
      const amount: bigint = deserializer.deserializeU64();

      return new ScriptFunctionCallVariantTransfer(
        to,
        amount
      );
    } else {
      throw new Error("Transaction payload not a script function payload")
    }
  }

  static SET_MESSAGE_CODE = Stdlib.fromHexString('a11ceb0b0400000005010002030205050705070c1408201000000001000100020c0a0200074d6573736167650b7365745f6d65737361676524163afcc6e33b0a9473852e18327fa9000001040b000b01110002');

  static ScriptArgs: {[name: string]: ScriptDef} = {
    SetMessage: {
      stdlibEncodeFunction: Stdlib.encodeSetMessageScript,
      stdlibDecodeFunction: Stdlib.decodeSetMessageScript,
      codeName: 'SET_MESSAGE',
      description: "",
      typeArgs: [],
      args: [
    {name: "message", type: {type: Types.Array, arrayType: {type: Types.U8}}}
      ]
    },
  }

  static ScriptFunctionArgs: {[name: string]: ScriptFunctionDef} = {

                InitializeErc20: {
      stdlibEncodeFunction: Stdlib.encodeInitializeErc20ScriptFunction,
      description: "",
      typeArgs: [],
      args: [
        {name: "total_supply", type: {type: Types.U64}}
      ]
    },
                

                SetMessage: {
      stdlibEncodeFunction: Stdlib.encodeSetMessageScriptFunction,
      description: "",
      typeArgs: [],
      args: [
        {name: "message", type: {type: Types.Array, arrayType: {type: Types.U8}}}
      ]
    },
                

                Transfer: {
      stdlibEncodeFunction: Stdlib.encodeTransferScriptFunction,
      description: "",
      typeArgs: [],
      args: [
        {name: "to", type: {type: Types.Address}}, {name: "amount", type: {type: Types.U64}}
      ]
    },
                
  }

}


export type ScriptDecoders = {
  User: {
    SetMessage: (type: string, message: DiemTypes.TransactionArgumentVariantU8Vector) => void;
    default: (type: keyof ScriptDecoders['User']) => void;
  };
};
