// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <blockdb.h>
#include <chain.h>
#include <chainparams.h>
#include <coins.h>
#include <config.h>
#include <consensus/validation.h>
#include <core_io.h>
#include <index/txindex.h>
#include <key_io.h>
#include <merkleblock.h>
#include <network.h>
#include <node/coin.h>
#include <node/context.h>
#include <node/psbt.h>
#include <node/transaction.h>
#include <policy/policy.h>
#include <primitives/transaction.h>
#include <psbt.h>
#include <random.h>
#include <rpc/blockchain.h>
#include <rpc/rawtransaction_util.h>
#include <rpc/server.h>
#include <rpc/util.h>
#include <script/script.h>
#include <script/sign.h>
#include <script/signingprovider.h>
#include <script/standard.h>
#include <txmempool.h>
#include <uint256.h>
#include <util/error.h>
#include <util/moneystr.h>
#include <util/strencodings.h>
#include <validation.h>
#include <validationinterface.h>
#ifdef ENABLE_WALLET
#include "wallet/rpcwallet.h"
#include "wallet/wallet.h"
#endif

#include <cstdint>
#include <numeric>

#include <univalue.h>

static void TxToJSON(const CTransaction &tx, const BlockHash &hashBlock,
                     UniValue &entry) {
    // Call into TxToUniv() in bitcoin-common to decode the transaction hex.
    //
    // Blockchain contextual information (confirmations and blocktime) is not
    // available to code in bitcoin-common, so we query them here and push the
    // data into the returned UniValue.
    TxToUniv(tx, uint256(), entry, true, RPCSerializationFlags());

    if (!hashBlock.IsNull()) {
        LOCK(cs_main);

        entry.pushKV("blockhash", hashBlock.GetHex());
        CBlockIndex *pindex = LookupBlockIndex(hashBlock);
        if (pindex) {
            if (::ChainActive().Contains(pindex)) {
                entry.pushKV("confirmations",
                             1 + ::ChainActive().Height() - pindex->nHeight);
                entry.pushKV("time", pindex->GetBlockTime());
                entry.pushKV("blocktime", pindex->GetBlockTime());
            } else {
                entry.pushKV("confirmations", 0);
            }
        }
    }
}

static UniValue getrawtransaction(const Config &config,
                                  const JSONRPCRequest &request) {
    RPCHelpMan{
        "getrawtransaction",
        "By default this function only works for mempool transactions. When "
        "called with a blockhash\n"
        "argument, getrawtransaction will return the transaction if the "
        "specified block is available and\n"
        "the transaction is found in that block. When called without a "
        "blockhash argument, getrawtransaction\n"
        "will return the transaction if it is in the mempool, or if -txindex "
        "is enabled and the transaction\n"
        "is in a block in the blockchain.\n"

        "\nReturn the raw transaction data.\n"
        "\nIf verbose is 'true', returns an Object with information about "
        "'txid'.\n"
        "If verbose is 'false' or omitted, returns a string that is "
        "serialized, hex-encoded data for 'txid'.\n",
        {
            {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO,
             "The transaction id"},
            {"verbose", RPCArg::Type::BOOL, /* default */ "false",
             "If false, return a string, otherwise return a json object"},
            {"blockhash", RPCArg::Type::STR_HEX,
             RPCArg::Optional::OMITTED_NAMED_ARG,
             "The block in which to look for the transaction"},
        },
        {
            RPCResult{"if verbose is not set or set to false",
                      RPCResult::Type::STR, "data",
                      "The serialized, hex-encoded data for 'txid'"},
            RPCResult{
                "if verbose is set to true",
                RPCResult::Type::OBJ,
                "",
                "",
                {
                    {RPCResult::Type::BOOL, "in_active_chain",
                     "Whether specified block is in the active chain or not "
                     "(only present with explicit \"blockhash\" argument)"},
                    {RPCResult::Type::STR_HEX, "hex",
                     "The serialized, hex-encoded data for 'txid'"},
                    {RPCResult::Type::STR_HEX, "txid",
                     "The transaction id (same as provided)"},
                    {RPCResult::Type::STR_HEX, "hash", "The transaction hash"},
                    {RPCResult::Type::NUM, "size",
                     "The serialized transaction size"},
                    {RPCResult::Type::NUM, "version", "The version"},
                    {RPCResult::Type::NUM_TIME, "locktime", "The lock time"},
                    {RPCResult::Type::ARR,
                     "vin",
                     "",
                     {
                         {RPCResult::Type::OBJ,
                          "",
                          "",
                          {
                              {RPCResult::Type::STR_HEX, "txid",
                               "The transaction id"},
                              {RPCResult::Type::STR, "vout", ""},
                              {RPCResult::Type::OBJ,
                               "scriptSig",
                               "The script",
                               {
                                   {RPCResult::Type::STR, "asm", "asm"},
                                   {RPCResult::Type::STR_HEX, "hex", "hex"},
                               }},
                              {RPCResult::Type::NUM, "sequence",
                               "The script sequence number"},
                          }},
                     }},
                    {RPCResult::Type::ARR,
                     "vout",
                     "",
                     {
                         {RPCResult::Type::OBJ,
                          "",
                          "",
                          {
                              {RPCResult::Type::NUM, "value",
                               "The value in " + CURRENCY_UNIT},
                              {RPCResult::Type::NUM, "n", "index"},
                              {RPCResult::Type::OBJ,
                               "scriptPubKey",
                               "",
                               {
                                   {RPCResult::Type::STR, "asm", "the asm"},
                                   {RPCResult::Type::STR, "hex", "the hex"},
                                   {RPCResult::Type::NUM, "reqSigs",
                                    "The required sigs"},
                                   {RPCResult::Type::STR, "type",
                                    "The type, eg 'pubkeyhash'"},
                                   {RPCResult::Type::ARR,
                                    "addresses",
                                    "",
                                    {
                                        {RPCResult::Type::STR, "address",
                                         "bitcoin address"},
                                    }},
                               }},
                          }},
                     }},
                    {RPCResult::Type::STR_HEX, "blockhash", "the block hash"},
                    {RPCResult::Type::NUM, "confirmations",
                     "The confirmations"},
                    {RPCResult::Type::NUM_TIME, "blocktime",
                     "The block time expressed in " + UNIX_EPOCH_TIME},
                    {RPCResult::Type::NUM, "time", "Same as \"blocktime\""},
                }},
        },
        RPCExamples{HelpExampleCli("getrawtransaction", "\"mytxid\"") +
                    HelpExampleCli("getrawtransaction", "\"mytxid\" true") +
                    HelpExampleRpc("getrawtransaction", "\"mytxid\", true") +
                    HelpExampleCli("getrawtransaction",
                                   "\"mytxid\" false \"myblockhash\"") +
                    HelpExampleCli("getrawtransaction",
                                   "\"mytxid\" true \"myblockhash\"")},
    }
        .Check(request);

    bool in_active_chain = true;
    TxId txid = TxId(ParseHashV(request.params[0], "parameter 1"));
    CBlockIndex *blockindex = nullptr;

    const CChainParams &params = config.GetChainParams();
    if (txid == params.GenesisBlock().hashMerkleRoot) {
        // Special exception for the genesis block coinbase transaction
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY,
                           "The genesis block coinbase is not considered an "
                           "ordinary transaction and cannot be retrieved");
    }

    // Accept either a bool (true) or a num (>=1) to indicate verbose output.
    bool fVerbose = false;
    if (!request.params[1].isNull()) {
        fVerbose = request.params[1].isNum()
                       ? (request.params[1].get_int() != 0)
                       : request.params[1].get_bool();
    }

    if (!request.params[2].isNull()) {
        LOCK(cs_main);

        BlockHash blockhash(ParseHashV(request.params[2], "parameter 3"));
        blockindex = LookupBlockIndex(blockhash);
        if (!blockindex) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY,
                               "Block hash not found");
        }
        in_active_chain = ::ChainActive().Contains(blockindex);
    }

    bool f_txindex_ready = false;
    if (g_txindex && !blockindex) {
        f_txindex_ready = g_txindex->BlockUntilSyncedToCurrentChain();
    }

    CTransactionRef tx;
    BlockHash hash_block;
    if (!GetTransaction(txid, tx, params.GetConsensus(), hash_block,
                        blockindex)) {
        std::string errmsg;
        if (blockindex) {
            if (!blockindex->nStatus.hasData()) {
                throw JSONRPCError(RPC_MISC_ERROR, "Block not available");
            }
            errmsg = "No such transaction found in the provided block";
        } else if (!g_txindex) {
            errmsg = "No such mempool transaction. Use -txindex or provide a "
                     "block hash to enable blockchain transaction queries";
        } else if (!f_txindex_ready) {
            errmsg = "No such mempool transaction. Blockchain transactions are "
                     "still in the process of being indexed";
        } else {
            errmsg = "No such mempool or blockchain transaction";
        }
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY,
                           errmsg +
                               ". Use gettransaction for wallet transactions.");
    }

    if (!fVerbose) {
        return EncodeHexTx(*tx, RPCSerializationFlags());
    }

    UniValue result(UniValue::VOBJ);
    if (blockindex) {
        result.pushKV("in_active_chain", in_active_chain);
    }
    TxToJSON(*tx, hash_block, result);
    return result;
}

static UniValue gettxoutproof(const Config &config,
                              const JSONRPCRequest &request) {
    RPCHelpMan{
        "gettxoutproof",
        "Returns a hex-encoded proof that \"txid\" was included in a block.\n"
        "\nNOTE: By default this function only works sometimes. "
        "This is when there is an\n"
        "unspent output in the utxo for this transaction. To make it always "
        "work,\n"
        "you need to maintain a transaction index, using the -txindex command "
        "line option or\n"
        "specify the block in which the transaction is included manually (by "
        "blockhash).\n",
        {
            {
                "txids",
                RPCArg::Type::ARR,
                RPCArg::Optional::NO,
                "A json array of txids to filter",
                {
                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED,
                     "A transaction hash"},
                },
            },
            {"blockhash", RPCArg::Type::STR_HEX,
             RPCArg::Optional::OMITTED_NAMED_ARG,
             "If specified, looks for txid in the block with this hash"},
        },
        RPCResult{
            RPCResult::Type::STR, "data",
            "A string that is a serialized, hex-encoded data for the proof."},
        RPCExamples{""},
    }
        .Check(request);

    std::set<TxId> setTxIds;
    TxId oneTxId;
    UniValue txids = request.params[0].get_array();
    for (unsigned int idx = 0; idx < txids.size(); idx++) {
        const UniValue &utxid = txids[idx];
        TxId txid(ParseHashV(utxid, "txid"));
        if (setTxIds.count(txid)) {
            throw JSONRPCError(
                RPC_INVALID_PARAMETER,
                std::string("Invalid parameter, duplicated txid: ") +
                    utxid.get_str());
        }

        setTxIds.insert(txid);
        oneTxId = txid;
    }

    CBlockIndex *pblockindex = nullptr;

    BlockHash hashBlock;
    if (!request.params[1].isNull()) {
        LOCK(cs_main);
        hashBlock = BlockHash(ParseHashV(request.params[1], "blockhash"));
        pblockindex = LookupBlockIndex(hashBlock);
        if (!pblockindex) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");
        }
    } else {
        LOCK(cs_main);
        // Loop through txids and try to find which block they're in. Exit loop
        // once a block is found.
        for (const auto &txid : setTxIds) {
            const Coin &coin =
                AccessByTxid(::ChainstateActive().CoinsTip(), txid);
            if (!coin.IsSpent()) {
                pblockindex = ::ChainActive()[coin.GetHeight()];
                break;
            }
        }
    }

    // Allow txindex to catch up if we need to query it and before we acquire
    // cs_main.
    if (g_txindex && !pblockindex) {
        g_txindex->BlockUntilSyncedToCurrentChain();
    }

    const Consensus::Params &params = config.GetChainParams().GetConsensus();

    LOCK(cs_main);

    if (pblockindex == nullptr) {
        CTransactionRef tx;
        if (!GetTransaction(oneTxId, tx, params, hashBlock) ||
            hashBlock.IsNull()) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY,
                               "Transaction not yet in block");
        }

        pblockindex = LookupBlockIndex(hashBlock);
        if (!pblockindex) {
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Transaction index corrupt");
        }
    }

    CBlock block;
    if (!ReadBlockFromDisk(block, pblockindex, params)) {
        throw JSONRPCError(RPC_INTERNAL_ERROR, "Can't read block from disk");
    }

    unsigned int ntxFound = 0;
    for (const auto &tx : block.vtx) {
        if (setTxIds.count(tx->GetId())) {
            ntxFound++;
        }
    }

    if (ntxFound != setTxIds.size()) {
        throw JSONRPCError(
            RPC_INVALID_ADDRESS_OR_KEY,
            "Not all transactions found in specified or retrieved block");
    }

    CDataStream ssMB(SER_NETWORK, PROTOCOL_VERSION);
    CMerkleBlock mb(block, setTxIds);
    ssMB << mb;
    std::string strHex = HexStr(ssMB.begin(), ssMB.end());
    return strHex;
}

static UniValue verifytxoutproof(const Config &config,
                                 const JSONRPCRequest &request) {
    RPCHelpMan{
        "verifytxoutproof",
        "Verifies that a proof points to a transaction in a block, returning "
        "the transaction it commits to\n"
        "and throwing an RPC error if the block is not in our best chain\n",
        {
            {"proof", RPCArg::Type::STR_HEX, RPCArg::Optional::NO,
             "The hex-encoded proof generated by gettxoutproof"},
        },
        RPCResult{RPCResult::Type::ARR,
                  "",
                  "",
                  {
                      {RPCResult::Type::STR_HEX, "txid",
                       "The txid(s) which the proof commits to, or empty array "
                       "if the proof can not be validated."},
                  }},
        RPCExamples{""},
    }
        .Check(request);

    CDataStream ssMB(ParseHexV(request.params[0], "proof"), SER_NETWORK,
                     PROTOCOL_VERSION);
    CMerkleBlock merkleBlock;
    ssMB >> merkleBlock;

    UniValue res(UniValue::VARR);

    std::vector<uint256> vMatch;
    std::vector<size_t> vIndex;
    if (merkleBlock.txn.ExtractMatches(vMatch, vIndex) !=
        merkleBlock.header.hashMerkleRoot) {
        return res;
    }

    LOCK(cs_main);

    const CBlockIndex *pindex = LookupBlockIndex(merkleBlock.header.GetHash());
    if (!pindex || !::ChainActive().Contains(pindex) || pindex->nTx == 0) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY,
                           "Block not found in chain");
    }

    // Check if proof is valid, only add results if so
    if (pindex->nTx == merkleBlock.txn.GetNumTransactions()) {
        for (const uint256 &hash : vMatch) {
            res.push_back(hash.GetHex());
        }
    }

    return res;
}

static UniValue createrawtransaction(const Config &config,
                                     const JSONRPCRequest &request) {
    RPCHelpMan{
        "createrawtransaction",
        "Create a transaction spending the given inputs and creating new "
        "outputs.\n"
        "Outputs can be addresses or data.\n"
        "Returns hex-encoded raw transaction.\n"
        "Note that the transaction's inputs are not signed, and\n"
        "it is not stored in the wallet or transmitted to the network.\n",
        {
            {
                "inputs",
                RPCArg::Type::ARR,
                RPCArg::Optional::NO,
                "A json array of json objects",
                {
                    {
                        "",
                        RPCArg::Type::OBJ,
                        RPCArg::Optional::OMITTED,
                        "",
                        {
                            {"txid", RPCArg::Type::STR_HEX,
                             RPCArg::Optional::NO, "The transaction id"},
                            {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO,
                             "The output number"},
                            {"sequence", RPCArg::Type::NUM, /* default */
                             "depends on the value of the 'locktime' argument",
                             "The sequence number"},
                        },
                    },
                },
            },
            {
                "outputs",
                RPCArg::Type::ARR,
                RPCArg::Optional::NO,
                "a json array with outputs (key-value pairs), where none of "
                "the keys are duplicated.\n"
                "That is, each address can only appear once and there can only "
                "be one 'data' object.\n"
                "For compatibility reasons, a dictionary, which holds the "
                "key-value pairs directly, is also\n"
                "                             accepted as second parameter.",
                {
                    {
                        "",
                        RPCArg::Type::OBJ,
                        RPCArg::Optional::OMITTED,
                        "",
                        {
                            {"address", RPCArg::Type::AMOUNT,
                             RPCArg::Optional::NO,
                             "A key-value pair. The key (string) is the "
                             "bitcoin address, the value (float or string) is "
                             "the amount in " +
                                 CURRENCY_UNIT},
                        },
                    },
                    {
                        "",
                        RPCArg::Type::OBJ,
                        RPCArg::Optional::OMITTED,
                        "",
                        {
                            {"data", RPCArg::Type::STR_HEX,
                             RPCArg::Optional::NO,
                             "A key-value pair. The key must be \"data\", the "
                             "value is hex-encoded data"},
                        },
                    },
                },
            },
            {"locktime", RPCArg::Type::NUM, /* default */ "0",
             "Raw locktime. Non-0 value also locktime-activates inputs"},
        },
        RPCResult{RPCResult::Type::STR_HEX, "transaction",
                  "hex string of the transaction"},
        RPCExamples{
            HelpExampleCli("createrawtransaction",
                           "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]"
                           "\" \"[{\\\"address\\\":0.01}]\"") +
            HelpExampleCli("createrawtransaction",
                           "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]"
                           "\" \"[{\\\"data\\\":\\\"00010203\\\"}]\"") +
            HelpExampleRpc("createrawtransaction",
                           "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]"
                           "\", \"[{\\\"address\\\":0.01}]\"") +
            HelpExampleRpc("createrawtransaction",
                           "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]"
                           "\", \"[{\\\"data\\\":\\\"00010203\\\"}]\"")},
    }
        .Check(request);

    RPCTypeCheck(request.params,
                 {UniValue::VARR,
                  UniValueType(), // ARR or OBJ, checked later
                  UniValue::VNUM},
                 true);

    CMutableTransaction rawTx =
        ConstructTransaction(config.GetChainParams(), request.params[0],
                             request.params[1], request.params[2]);

    return EncodeHexTx(CTransaction(rawTx));
}

static UniValue decoderawtransaction(const Config &config,
                                     const JSONRPCRequest &request) {
    RPCHelpMan{
        "decoderawtransaction",
        "Return a JSON object representing the serialized, hex-encoded "
        "transaction.\n",
        {
            {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO,
             "The transaction hex string"},
        },
        RPCResult{
            RPCResult::Type::OBJ,
            "",
            "",
            {
                {RPCResult::Type::STR_HEX, "txid", "The transaction id"},
                {RPCResult::Type::STR_HEX, "hash", "The transaction hash"},
                {RPCResult::Type::NUM, "size", "The transaction size"},
                {RPCResult::Type::NUM, "version", "The version"},
                {RPCResult::Type::NUM_TIME, "locktime", "The lock time"},
                {RPCResult::Type::ARR,
                 "vin",
                 "",
                 {
                     {RPCResult::Type::OBJ,
                      "",
                      "",
                      {
                          {RPCResult::Type::STR_HEX, "txid",
                           "The transaction id"},
                          {RPCResult::Type::NUM, "vout", "The output number"},
                          {RPCResult::Type::OBJ,
                           "scriptSig",
                           "The script",
                           {
                               {RPCResult::Type::STR, "asm", "asm"},
                               {RPCResult::Type::STR_HEX, "hex", "hex"},
                           }},
                          {RPCResult::Type::NUM, "sequence",
                           "The script sequence number"},
                      }},
                 }},
                {RPCResult::Type::ARR,
                 "vout",
                 "",
                 {
                     {RPCResult::Type::OBJ,
                      "",
                      "",
                      {
                          {RPCResult::Type::NUM, "value",
                           "The value in " + CURRENCY_UNIT},
                          {RPCResult::Type::NUM, "n", "index"},
                          {RPCResult::Type::OBJ,
                           "scriptPubKey",
                           "",
                           {
                               {RPCResult::Type::STR, "asm", "the asm"},
                               {RPCResult::Type::STR_HEX, "hex", "the hex"},
                               {RPCResult::Type::NUM, "reqSigs",
                                "The required sigs"},
                               {RPCResult::Type::STR, "type",
                                "The type, eg 'pubkeyhash'"},
                               {RPCResult::Type::ARR,
                                "addresses",
                                "",
                                {
                                    {RPCResult::Type::STR, "address",
                                     "bitcoin address"},
                                }},
                           }},
                      }},
                 }},
            }},
        RPCExamples{HelpExampleCli("decoderawtransaction", "\"hexstring\"") +
                    HelpExampleRpc("decoderawtransaction", "\"hexstring\"")},
    }
        .Check(request);

    RPCTypeCheck(request.params, {UniValue::VSTR});

    CMutableTransaction mtx;

    if (!DecodeHexTx(mtx, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    UniValue result(UniValue::VOBJ);
    TxToUniv(CTransaction(std::move(mtx)), uint256(), result, false);

    return result;
}

static std::string GetAllOutputTypes() {
    std::string ret;
    for (int i = TX_NONSTANDARD; i <= TX_NULL_DATA; ++i) {
        if (i != TX_NONSTANDARD) {
            ret += ", ";
        }
        ret += GetTxnOutputType(static_cast<txnouttype>(i));
    }
    return ret;
}

static UniValue decodescript(const Config &config,
                             const JSONRPCRequest &request) {
    RPCHelpMan{
        "decodescript",
        "Decode a hex-encoded script.\n",
        {
            {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO,
             "the hex-encoded script"},
        },
        RPCResult{
            RPCResult::Type::OBJ,
            "",
            "",
            {
                {RPCResult::Type::STR, "asm", "Script public key"},
                {RPCResult::Type::STR, "type",
                 "The output type (e.g. " + GetAllOutputTypes() + ")"},
                {RPCResult::Type::NUM, "reqSigs", "The required signatures"},
                {RPCResult::Type::ARR,
                 "addresses",
                 "",
                 {
                     {RPCResult::Type::STR, "address", "bitcoin address"},
                 }},
                {RPCResult::Type::STR, "p2sh",
                 "address of P2SH script wrapping this redeem script (not "
                 "returned if the script is already a P2SH)"},
            }},
        RPCExamples{HelpExampleCli("decodescript", "\"hexstring\"") +
                    HelpExampleRpc("decodescript", "\"hexstring\"")},
    }
        .Check(request);

    RPCTypeCheck(request.params, {UniValue::VSTR});

    UniValue r(UniValue::VOBJ);
    CScript script;
    if (request.params[0].get_str().size() > 0) {
        std::vector<uint8_t> scriptData(
            ParseHexV(request.params[0], "argument"));
        script = CScript(scriptData.begin(), scriptData.end());
    } else {
        // Empty scripts are valid.
    }

    ScriptPubKeyToUniv(script, r, /* fIncludeHex */ false);

    UniValue type;
    type = find_value(r, "type");

    if (type.isStr() && type.get_str() != "scripthash") {
        // P2SH cannot be wrapped in a P2SH. If this script is already a P2SH,
        // don't return the address for a P2SH of the P2SH.
        r.pushKV("p2sh", EncodeDestination(ScriptHash(script), config));
    }

    return r;
}

static UniValue combinerawtransaction(const Config &config,
                                      const JSONRPCRequest &request) {
    RPCHelpMan{
        "combinerawtransaction",
        "Combine multiple partially signed transactions into one "
        "transaction.\n"
        "The combined transaction may be another partially signed transaction "
        "or a \n"
        "fully signed transaction.",
        {
            {
                "txs",
                RPCArg::Type::ARR,
                RPCArg::Optional::NO,
                "A json array of hex strings of partially signed "
                "transactions",
                {
                    {"hexstring", RPCArg::Type::STR_HEX,
                     RPCArg::Optional::OMITTED, "A transaction hash"},
                },
            },
        },
        RPCResult{RPCResult::Type::STR, "",
                  "The hex-encoded raw transaction with signature(s)"},
        RPCExamples{HelpExampleCli("combinerawtransaction",
                                   "[\"myhex1\", \"myhex2\", \"myhex3\"]")},
    }
        .Check(request);

    UniValue txs = request.params[0].get_array();
    std::vector<CMutableTransaction> txVariants(txs.size());

    for (unsigned int idx = 0; idx < txs.size(); idx++) {
        if (!DecodeHexTx(txVariants[idx], txs[idx].get_str())) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                               strprintf("TX decode failed for tx %d", idx));
        }
    }

    if (txVariants.empty()) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Missing transactions");
    }

    // mergedTx will end up with all the signatures; it
    // starts as a clone of the rawtx:
    CMutableTransaction mergedTx(txVariants[0]);

    // Fetch previous transactions (inputs):
    CCoinsView viewDummy;
    CCoinsViewCache view(&viewDummy);
    {
        const CTxMemPool &mempool = EnsureMemPool(request.context);
        LOCK(cs_main);
        LOCK(mempool.cs);
        CCoinsViewCache &viewChain = ::ChainstateActive().CoinsTip();
        CCoinsViewMemPool viewMempool(&viewChain, mempool);
        // temporarily switch cache backend to db+mempool view
        view.SetBackend(viewMempool);

        for (const CTxIn &txin : mergedTx.vin) {
            // Load entries from viewChain into view; can fail.
            view.AccessCoin(txin.prevout);
        }

        // switch back to avoid locking mempool for too long
        view.SetBackend(viewDummy);
    }

    // Use CTransaction for the constant parts of the
    // transaction to avoid rehashing.
    const CTransaction txConst(mergedTx);
    // Sign what we can:
    for (size_t i = 0; i < mergedTx.vin.size(); i++) {
        CTxIn &txin = mergedTx.vin[i];
        const Coin &coin = view.AccessCoin(txin.prevout);
        if (coin.IsSpent()) {
            throw JSONRPCError(RPC_VERIFY_ERROR,
                               "Input not found or already spent");
        }
        SignatureData sigdata;

        const CTxOut &txout = coin.GetTxOut();

        // ... and merge in other signatures:
        for (const CMutableTransaction &txv : txVariants) {
            if (txv.vin.size() > i) {
                sigdata.MergeSignatureData(DataFromTransaction(txv, i, txout));
            }
        }
        ProduceSignature(
            DUMMY_SIGNING_PROVIDER,
            MutableTransactionSignatureCreator(&mergedTx, i, txout.nValue),
            txout.scriptPubKey, sigdata);

        UpdateInput(txin, sigdata);
    }

    return EncodeHexTx(CTransaction(mergedTx));
}

static UniValue signrawtransactionwithkey(const Config &config,
                                          const JSONRPCRequest &request) {
    RPCHelpMan{
        "signrawtransactionwithkey",
        "Sign inputs for raw transaction (serialized, hex-encoded).\n"
        "The second argument is an array of base58-encoded private\n"
        "keys that will be the only keys used to sign the transaction.\n"
        "The third optional argument (may be null) is an array of previous "
        "transaction outputs that\n"
        "this transaction depends on but may not yet be in the block chain.\n",
        {
            {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO,
             "The transaction hex string"},
            {
                "privkeys",
                RPCArg::Type::ARR,
                RPCArg::Optional::NO,
                "A json array of base58-encoded private keys for signing",
                {
                    {"privatekey", RPCArg::Type::STR, RPCArg::Optional::OMITTED,
                     "private key in base58-encoding"},
                },
            },
            {
                "prevtxs",
                RPCArg::Type::ARR,
                RPCArg::Optional::OMITTED_NAMED_ARG,
                "A json array of previous dependent transaction outputs",
                {
                    {
                        "",
                        RPCArg::Type::OBJ,
                        RPCArg::Optional::OMITTED,
                        "",
                        {
                            {"txid", RPCArg::Type::STR_HEX,
                             RPCArg::Optional::NO, "The transaction id"},
                            {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO,
                             "The output number"},
                            {"scriptPubKey", RPCArg::Type::STR_HEX,
                             RPCArg::Optional::NO, "script key"},
                            {"redeemScript", RPCArg::Type::STR_HEX,
                             RPCArg::Optional::OMITTED,
                             "(required for P2SH) redeem script"},
                            {"amount", RPCArg::Type::AMOUNT,
                             RPCArg::Optional::NO, "The amount spent"},
                        },
                    },
                },
            },
            {"sighashtype", RPCArg::Type::STR, /* default */ "ALL|FORKID",
             "The signature hash type. Must be one of:\n"
             "       \"ALL|FORKID\"\n"
             "       \"NONE|FORKID\"\n"
             "       \"SINGLE|FORKID\"\n"
             "       \"ALL|FORKID|ANYONECANPAY\"\n"
             "       \"NONE|FORKID|ANYONECANPAY\"\n"
             "       \"SINGLE|FORKID|ANYONECANPAY\""},
        },
        RPCResult{
            RPCResult::Type::OBJ,
            "",
            "",
            {
                {RPCResult::Type::STR_HEX, "hex",
                 "The hex-encoded raw transaction with signature(s)"},
                {RPCResult::Type::BOOL, "complete",
                 "If the transaction has a complete set of signatures"},
                {RPCResult::Type::ARR,
                 "errors",
                 "Script verification errors (if there are any)",
                 {
                     {RPCResult::Type::OBJ,
                      "",
                      "",
                      {
                          {RPCResult::Type::STR_HEX, "txid",
                           "The hash of the referenced, previous transaction"},
                          {RPCResult::Type::NUM, "vout",
                           "The index of the output to spent and used as "
                           "input"},
                          {RPCResult::Type::STR_HEX, "scriptSig",
                           "The hex-encoded signature script"},
                          {RPCResult::Type::NUM, "sequence",
                           "Script sequence number"},
                          {RPCResult::Type::STR, "error",
                           "Verification or signing error related to the "
                           "input"},
                      }},
                 }},
            }},
        RPCExamples{
            HelpExampleCli("signrawtransactionwithkey",
                           "\"myhex\" \"[\\\"key1\\\",\\\"key2\\\"]\"") +
            HelpExampleRpc("signrawtransactionwithkey",
                           "\"myhex\", \"[\\\"key1\\\",\\\"key2\\\"]\"")},
    }
        .Check(request);

    RPCTypeCheck(
        request.params,
        {UniValue::VSTR, UniValue::VARR, UniValue::VARR, UniValue::VSTR}, true);

    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    FillableSigningProvider keystore;
    const UniValue &keys = request.params[1].get_array();
    for (size_t idx = 0; idx < keys.size(); ++idx) {
        UniValue k = keys[idx];
        CKey key = DecodeSecret(k.get_str());
        if (!key.IsValid()) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY,
                               "Invalid private key");
        }
        keystore.AddKey(key);
    }

    // Fetch previous transactions (inputs):
    std::map<COutPoint, Coin> coins;
    for (const CTxIn &txin : mtx.vin) {
        // Create empty map entry keyed by prevout.
        coins[txin.prevout];
    }
    NodeContext &node = EnsureNodeContext(request.context);
    FindCoins(node, coins);

    // Parse the prevtxs array
    ParsePrevouts(request.params[2], &keystore, coins);

    UniValue result(UniValue::VOBJ);
    SignTransaction(mtx, &keystore, coins, request.params[3], result);
    return result;
}

static UniValue sendrawtransaction(const Config &config,
                                   const JSONRPCRequest &request) {
    RPCHelpMan{
        "sendrawtransaction",
        "Submits raw transaction (serialized, hex-encoded) to local node and "
        "network.\n"
        "\nAlso see createrawtransaction and "
        "signrawtransactionwithkey calls.\n",
        {
            {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO,
             "The hex string of the raw transaction"},
            {"maxfeerate", RPCArg::Type::AMOUNT,
             /* default */
             FormatMoney(DEFAULT_MAX_RAW_TX_FEE_RATE.GetFeePerK()),
             "Reject transactions whose fee rate is higher than the specified "
             "value, expressed in " +
                 CURRENCY_UNIT + "/kB\nSet to 0 to accept any fee rate.\n"},
        },
        RPCResult{RPCResult::Type::STR_HEX, "", "The transaction hash in hex"},
        RPCExamples{
            "\nCreate a transaction\n" +
            HelpExampleCli(
                "createrawtransaction",
                "\"[{\\\"txid\\\" : \\\"mytxid\\\",\\\"vout\\\":0}]\" "
                "\"{\\\"myaddress\\\":0.01}\"") +
            "Sign the transaction, and get back the hex\n" +
            HelpExampleCli("signrawtransactionwithwallet", "\"myhex\"") +
            "\nSend the transaction (signed hex)\n" +
            HelpExampleCli("sendrawtransaction", "\"signedhex\"") +
            "\nAs a JSON-RPC call\n" +
            HelpExampleRpc("sendrawtransaction", "\"signedhex\"")},
    }
        .Check(request);

    RPCTypeCheck(request.params, {
                                     UniValue::VSTR,
                                     // NUM or BOOL, checked later
                                     UniValueType(),
                                 });

    // parse hex string from parameter
    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    CTransactionRef tx(MakeTransactionRef(std::move(mtx)));

    CFeeRate max_raw_tx_fee_rate = DEFAULT_MAX_RAW_TX_FEE_RATE;
    // TODO: temporary migration code for old clients. Remove in v0.22
    if (request.params[1].isBool()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER,
                           "Second argument must be numeric (maxfeerate) and "
                           "no longer supports a boolean. To allow a "
                           "transaction with high fees, set maxfeerate to 0.");
    } else if (!request.params[1].isNull()) {
        max_raw_tx_fee_rate = CFeeRate(AmountFromValue(request.params[1]));
    }

    int64_t virtual_size = GetVirtualTransactionSize(*tx);
    Amount max_raw_tx_fee = max_raw_tx_fee_rate.GetFee(virtual_size);

    std::string err_string;
    AssertLockNotHeld(cs_main);
    NodeContext &node = EnsureNodeContext(request.context);
    const TransactionError err = BroadcastTransaction(
        node, config, tx, err_string, max_raw_tx_fee, /*relay*/ true,
        /*wait_callback*/ true);
    if (err != TransactionError::OK) {
        throw JSONRPCTransactionError(err, err_string);
    }

    return tx->GetHash().GetHex();
}

static UniValue testmempoolaccept(const Config &config,
                                  const JSONRPCRequest &request) {
    RPCHelpMan{
        "testmempoolaccept",
        "Returns result of mempool acceptance tests indicating if raw"
        " transaction (serialized, hex-encoded) would be accepted"
        " by mempool.\n"
        "\nThis checks if the transaction violates the consensus or policy "
        "rules.\n"
        "\nSee sendrawtransaction call.\n",
        {
            {
                "rawtxs",
                RPCArg::Type::ARR,
                RPCArg::Optional::NO,
                "An array of hex strings of raw transactions.\n"
                "                             Length must be one for now.",
                {
                    {"rawtx", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED,
                     ""},
                },
            },
            {"maxfeerate", RPCArg::Type::AMOUNT,
             /* default */
             FormatMoney(DEFAULT_MAX_RAW_TX_FEE_RATE.GetFeePerK()),
             "Reject transactions whose fee rate is higher than the specified "
             "value, expressed in " +
                 CURRENCY_UNIT + "/kB\n"},
        },
        RPCResult{RPCResult::Type::ARR,
                  "",
                  "The result of the mempool acceptance test for each raw "
                  "transaction in the input array.\n"
                  "Length is exactly one for now.",
                  {
                      {RPCResult::Type::OBJ,
                       "",
                       "",
                       {
                           {RPCResult::Type::STR_HEX, "txid",
                            "The transaction hash in hex"},
                           {RPCResult::Type::BOOL, "allowed",
                            "If the mempool allows this tx to be inserted"},
                           {RPCResult::Type::STR, "reject-reason",
                            "Rejection string (only present when 'allowed' is "
                            "false)"},
                       }},
                  }},
        RPCExamples{
            "\nCreate a transaction\n" +
            HelpExampleCli(
                "createrawtransaction",
                "\"[{\\\"txid\\\" : \\\"mytxid\\\",\\\"vout\\\":0}]\" "
                "\"{\\\"myaddress\\\":0.01}\"") +
            "Sign the transaction, and get back the hex\n" +
            HelpExampleCli("signrawtransactionwithwallet", "\"myhex\"") +
            "\nTest acceptance of the transaction (signed hex)\n" +
            HelpExampleCli("testmempoolaccept", "[\"signedhex\"]") +
            "\nAs a JSON-RPC call\n" +
            HelpExampleRpc("testmempoolaccept", "[\"signedhex\"]")},
    }
        .Check(request);

    RPCTypeCheck(request.params, {
                                     UniValue::VARR,
                                     // NUM or BOOL, checked later
                                     UniValueType(),
                                 });

    if (request.params[0].get_array().size() != 1) {
        throw JSONRPCError(
            RPC_INVALID_PARAMETER,
            "Array must contain exactly one raw transaction for now");
    }

    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_array()[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }
    CTransactionRef tx(MakeTransactionRef(std::move(mtx)));
    const TxId &txid = tx->GetId();

    CFeeRate max_raw_tx_fee_rate = DEFAULT_MAX_RAW_TX_FEE_RATE;
    // TODO: temporary migration code for old clients. Remove in v0.22
    if (request.params[1].isBool()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER,
                           "Second argument must be numeric (maxfeerate) and "
                           "no longer supports a boolean. To allow a "
                           "transaction with high fees, set maxfeerate to 0.");
    } else if (!request.params[1].isNull()) {
        max_raw_tx_fee_rate = CFeeRate(AmountFromValue(request.params[1]));
    }

    CTxMemPool &mempool = EnsureMemPool(request.context);
    int64_t virtual_size = GetVirtualTransactionSize(*tx);
    Amount max_raw_tx_fee = max_raw_tx_fee_rate.GetFee(virtual_size);

    UniValue result(UniValue::VARR);
    UniValue result_0(UniValue::VOBJ);
    result_0.pushKV("txid", txid.GetHex());

    TxValidationState state;
    bool test_accept_res;
    {
        LOCK(cs_main);
        test_accept_res = AcceptToMemoryPool(
            config, mempool, state, std::move(tx), false /* bypass_limits */,
            max_raw_tx_fee, true /* test_accept */);
    }
    result_0.pushKV("allowed", test_accept_res);
    if (!test_accept_res) {
        if (state.IsInvalid()) {
            if (state.GetResult() == TxValidationResult::TX_MISSING_INPUTS) {
                result_0.pushKV("reject-reason", "missing-inputs");
            } else {
                result_0.pushKV("reject-reason",
                                strprintf("%s", state.GetRejectReason()));
            }
        } else {
            result_0.pushKV("reject-reason", state.GetRejectReason());
        }
    }

    result.push_back(std::move(result_0));
    return result;
}

static std::string WriteHDKeypath(std::vector<uint32_t> &keypath) {
    std::string keypath_str = "m";
    for (uint32_t num : keypath) {
        keypath_str += "/";
        bool hardened = false;
        if (num & 0x80000000) {
            hardened = true;
            num &= ~0x80000000;
        }

        keypath_str += std::to_string(num);
        if (hardened) {
            keypath_str += "'";
        }
    }
    return keypath_str;
}

static UniValue decodepsbt(const Config &config,
                           const JSONRPCRequest &request) {
    RPCHelpMan{
        "decodepsbt",
        "Return a JSON object representing the serialized, base64-encoded "
        "partially signed Bitcoin transaction.\n",
        {
            {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO,
             "The PSBT base64 string"},
        },
        RPCResult{
            RPCResult::Type::OBJ,
            "",
            "",
            {
                {RPCResult::Type::OBJ,
                 "tx",
                 "The decoded network-serialized unsigned transaction.",
                 {
                     {RPCResult::Type::ELISION, "",
                      "The layout is the same as the output of "
                      "decoderawtransaction."},
                 }},
                {RPCResult::Type::OBJ_DYN,
                 "unknown",
                 "The unknown global fields",
                 {
                     {RPCResult::Type::STR_HEX, "key",
                      "(key-value pair) An unknown key-value pair"},
                 }},
                {RPCResult::Type::ARR,
                 "inputs",
                 "",
                 {
                     {RPCResult::Type::OBJ,
                      "",
                      "",
                      {
                          {RPCResult::Type::OBJ,
                           "utxo",
                           /* optional */ true,
                           "Transaction output for UTXOs",
                           {
                               {RPCResult::Type::NUM, "amount",
                                "The value in " + CURRENCY_UNIT},
                               {RPCResult::Type::OBJ,
                                "scriptPubKey",
                                "",
                                {
                                    {RPCResult::Type::STR, "asm", "The asm"},
                                    {RPCResult::Type::STR_HEX, "hex",
                                     "The hex"},
                                    {RPCResult::Type::STR, "type",
                                     "The type, eg 'pubkeyhash'"},
                                    {RPCResult::Type::STR, "address",
                                     " Bitcoin address if there is one"},
                                }},
                           }},
                          {RPCResult::Type::OBJ_DYN,
                           "partial_signatures",
                           /* optional */ true,
                           "",
                           {
                               {RPCResult::Type::STR, "pubkey",
                                "The public key and signature that corresponds "
                                "to it."},
                           }},
                          {RPCResult::Type::STR, "sighash", /* optional */ true,
                           "The sighash type to be used"},
                          {RPCResult::Type::OBJ,
                           "redeem_script",
                           /* optional */ true,
                           "",
                           {
                               {RPCResult::Type::STR, "asm", "The asm"},
                               {RPCResult::Type::STR_HEX, "hex", "The hex"},
                               {RPCResult::Type::STR, "type",
                                "The type, eg 'pubkeyhash'"},
                           }},
                          {RPCResult::Type::ARR,
                           "bip32_derivs",
                           /* optional */ true,
                           "",
                           {
                               {RPCResult::Type::OBJ,
                                "pubkey",
                                /* optional */ true,
                                "The public key with the derivation path as "
                                "the value.",
                                {
                                    {RPCResult::Type::STR, "master_fingerprint",
                                     "The fingerprint of the master key"},
                                    {RPCResult::Type::STR, "path", "The path"},
                                }},
                           }},
                          {RPCResult::Type::OBJ,
                           "final_scriptsig",
                           /* optional */ true,
                           "",
                           {
                               {RPCResult::Type::STR, "asm", "The asm"},
                               {RPCResult::Type::STR, "hex", "The hex"},
                           }},
                          {RPCResult::Type::OBJ_DYN,
                           "unknown",
                           "The unknown global fields",
                           {
                               {RPCResult::Type::STR_HEX, "key",
                                "(key-value pair) An unknown key-value pair"},
                           }},
                      }},
                 }},
                {RPCResult::Type::ARR,
                 "outputs",
                 "",
                 {
                     {RPCResult::Type::OBJ,
                      "",
                      "",
                      {
                          {RPCResult::Type::OBJ,
                           "redeem_script",
                           /* optional */ true,
                           "",
                           {
                               {RPCResult::Type::STR, "asm", "The asm"},
                               {RPCResult::Type::STR_HEX, "hex", "The hex"},
                               {RPCResult::Type::STR, "type",
                                "The type, eg 'pubkeyhash'"},
                           }},
                          {RPCResult::Type::ARR,
                           "bip32_derivs",
                           /* optional */ true,
                           "",
                           {
                               {RPCResult::Type::OBJ,
                                "",
                                "",
                                {
                                    {RPCResult::Type::STR, "pubkey",
                                     "The public key this path corresponds to"},
                                    {RPCResult::Type::STR, "master_fingerprint",
                                     "The fingerprint of the master key"},
                                    {RPCResult::Type::STR, "path", "The path"},
                                }},
                           }},
                          {RPCResult::Type::OBJ_DYN,
                           "unknown",
                           "The unknown global fields",
                           {
                               {RPCResult::Type::STR_HEX, "key",
                                "(key-value pair) An unknown key-value pair"},
                           }},
                      }},
                 }},
                {RPCResult::Type::STR_AMOUNT, "fee", /* optional */ true,
                 "The transaction fee paid if all UTXOs slots in the PSBT have "
                 "been filled."},
            }},
        RPCExamples{HelpExampleCli("decodepsbt", "\"psbt\"")},
    }
        .Check(request);

    RPCTypeCheck(request.params, {UniValue::VSTR});

    // Unserialize the transactions
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                           strprintf("TX decode failed %s", error));
    }

    UniValue result(UniValue::VOBJ);

    // Add the decoded tx
    UniValue tx_univ(UniValue::VOBJ);
    TxToUniv(CTransaction(*psbtx.tx), uint256(), tx_univ, false);
    result.pushKV("tx", tx_univ);

    // Unknown data
    if (psbtx.unknown.size() > 0) {
        UniValue unknowns(UniValue::VOBJ);
        for (auto entry : psbtx.unknown) {
            unknowns.pushKV(HexStr(entry.first), HexStr(entry.second));
        }
        result.pushKV("unknown", unknowns);
    }

    // inputs
    Amount total_in = Amount::zero();
    bool have_all_utxos = true;
    UniValue inputs(UniValue::VARR);
    for (size_t i = 0; i < psbtx.inputs.size(); ++i) {
        const PSBTInput &input = psbtx.inputs[i];
        UniValue in(UniValue::VOBJ);
        // UTXOs
        if (!input.utxo.IsNull()) {
            const CTxOut &txout = input.utxo;

            UniValue out(UniValue::VOBJ);

            out.pushKV("amount", ValueFromAmount(txout.nValue));
            if (MoneyRange(txout.nValue) &&
                MoneyRange(total_in + txout.nValue)) {
                total_in += txout.nValue;
            } else {
                // Hack to just not show fee later
                have_all_utxos = false;
            }

            UniValue o(UniValue::VOBJ);
            ScriptToUniv(txout.scriptPubKey, o, true);
            out.pushKV("scriptPubKey", o);
            in.pushKV("utxo", out);
        } else {
            have_all_utxos = false;
        }

        // Partial sigs
        if (!input.partial_sigs.empty()) {
            UniValue partial_sigs(UniValue::VOBJ);
            for (const auto &sig : input.partial_sigs) {
                partial_sigs.pushKV(HexStr(sig.second.first),
                                    HexStr(sig.second.second));
            }
            in.pushKV("partial_signatures", partial_sigs);
        }

        // Sighash
        uint8_t sighashbyte = input.sighash_type.getRawSigHashType() & 0xff;
        if (sighashbyte > 0) {
            in.pushKV("sighash", SighashToStr(sighashbyte));
        }

        // Redeem script
        if (!input.redeem_script.empty()) {
            UniValue r(UniValue::VOBJ);
            ScriptToUniv(input.redeem_script, r, false);
            in.pushKV("redeem_script", r);
        }

        // keypaths
        if (!input.hd_keypaths.empty()) {
            UniValue keypaths(UniValue::VARR);
            for (auto entry : input.hd_keypaths) {
                UniValue keypath(UniValue::VOBJ);
                keypath.pushKV("pubkey", HexStr(entry.first));

                keypath.pushKV(
                    "master_fingerprint",
                    strprintf("%08x", ReadBE32(entry.second.fingerprint)));
                keypath.pushKV("path", WriteHDKeypath(entry.second.path));
                keypaths.push_back(keypath);
            }
            in.pushKV("bip32_derivs", keypaths);
        }

        // Final scriptSig
        if (!input.final_script_sig.empty()) {
            UniValue scriptsig(UniValue::VOBJ);
            scriptsig.pushKV("asm",
                             ScriptToAsmStr(input.final_script_sig, true));
            scriptsig.pushKV("hex", HexStr(input.final_script_sig));
            in.pushKV("final_scriptSig", scriptsig);
        }

        // Unknown data
        if (input.unknown.size() > 0) {
            UniValue unknowns(UniValue::VOBJ);
            for (auto entry : input.unknown) {
                unknowns.pushKV(HexStr(entry.first), HexStr(entry.second));
            }
            in.pushKV("unknown", unknowns);
        }

        inputs.push_back(in);
    }
    result.pushKV("inputs", inputs);

    // outputs
    Amount output_value = Amount::zero();
    UniValue outputs(UniValue::VARR);
    for (size_t i = 0; i < psbtx.outputs.size(); ++i) {
        const PSBTOutput &output = psbtx.outputs[i];
        UniValue out(UniValue::VOBJ);
        // Redeem script
        if (!output.redeem_script.empty()) {
            UniValue r(UniValue::VOBJ);
            ScriptToUniv(output.redeem_script, r, false);
            out.pushKV("redeem_script", r);
        }

        // keypaths
        if (!output.hd_keypaths.empty()) {
            UniValue keypaths(UniValue::VARR);
            for (auto entry : output.hd_keypaths) {
                UniValue keypath(UniValue::VOBJ);
                keypath.pushKV("pubkey", HexStr(entry.first));
                keypath.pushKV(
                    "master_fingerprint",
                    strprintf("%08x", ReadBE32(entry.second.fingerprint)));
                keypath.pushKV("path", WriteHDKeypath(entry.second.path));
                keypaths.push_back(keypath);
            }
            out.pushKV("bip32_derivs", keypaths);
        }

        // Unknown data
        if (output.unknown.size() > 0) {
            UniValue unknowns(UniValue::VOBJ);
            for (auto entry : output.unknown) {
                unknowns.pushKV(HexStr(entry.first), HexStr(entry.second));
            }
            out.pushKV("unknown", unknowns);
        }

        outputs.push_back(out);

        // Fee calculation
        if (MoneyRange(psbtx.tx->vout[i].nValue) &&
            MoneyRange(output_value + psbtx.tx->vout[i].nValue)) {
            output_value += psbtx.tx->vout[i].nValue;
        } else {
            // Hack to just not show fee later
            have_all_utxos = false;
        }
    }
    result.pushKV("outputs", outputs);
    if (have_all_utxos) {
        result.pushKV("fee", ValueFromAmount(total_in - output_value));
    }

    return result;
}

static UniValue combinepsbt(const Config &config,
                            const JSONRPCRequest &request) {
    RPCHelpMan{
        "combinepsbt",
        "Combine multiple partially signed Bitcoin transactions into one "
        "transaction.\n"
        "Implements the Combiner role.\n",
        {
            {
                "txs",
                RPCArg::Type::ARR,
                RPCArg::Optional::NO,
                "A json array of base64 strings of partially signed "
                "transactions",
                {
                    {"psbt", RPCArg::Type::STR, RPCArg::Optional::OMITTED,
                     "A base64 string of a PSBT"},
                },
            },
        },
        RPCResult{RPCResult::Type::STR, "",
                  "The base64-encoded partially signed transaction"},
        RPCExamples{HelpExampleCli(
            "combinepsbt", "[\"mybase64_1\", \"mybase64_2\", \"mybase64_3\"]")},
    }
        .Check(request);

    RPCTypeCheck(request.params, {UniValue::VARR}, true);

    // Unserialize the transactions
    std::vector<PartiallySignedTransaction> psbtxs;
    UniValue txs = request.params[0].get_array();
    if (txs.empty()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER,
                           "Parameter 'txs' cannot be empty");
    }
    for (size_t i = 0; i < txs.size(); ++i) {
        PartiallySignedTransaction psbtx;
        std::string error;
        if (!DecodeBase64PSBT(psbtx, txs[i].get_str(), error)) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                               strprintf("TX decode failed %s", error));
        }
        psbtxs.push_back(psbtx);
    }

    PartiallySignedTransaction merged_psbt;
    const TransactionError error = CombinePSBTs(merged_psbt, psbtxs);
    if (error != TransactionError::OK) {
        throw JSONRPCTransactionError(error);
    }

    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << merged_psbt;
    return EncodeBase64((uint8_t *)ssTx.data(), ssTx.size());
}

static UniValue finalizepsbt(const Config &config,
                             const JSONRPCRequest &request) {
    RPCHelpMan{
        "finalizepsbt",
        "Finalize the inputs of a PSBT. If the transaction is fully signed, it "
        "will produce a\n"
        "network serialized transaction which can be broadcast with "
        "sendrawtransaction. Otherwise a PSBT will be\n"
        "created which has the final_scriptSigfields filled for inputs that "
        "are complete.\n"
        "Implements the Finalizer and Extractor roles.\n",
        {
            {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO,
             "A base64 string of a PSBT"},
            {"extract", RPCArg::Type::BOOL, /* default */ "true",
             "If true and the transaction is complete,\n"
             "                             extract and return the complete "
             "transaction in normal network serialization instead of the "
             "PSBT."},
        },
        RPCResult{RPCResult::Type::OBJ,
                  "",
                  "",
                  {
                      {RPCResult::Type::STR, "psbt",
                       "The base64-encoded partially signed transaction if not "
                       "extracted"},
                      {RPCResult::Type::STR_HEX, "hex",
                       "The hex-encoded network transaction if extracted"},
                      {RPCResult::Type::BOOL, "complete",
                       "If the transaction has a complete set of signatures"},
                  }},
        RPCExamples{HelpExampleCli("finalizepsbt", "\"psbt\"")},
    }
        .Check(request);

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VBOOL}, true);

    // Unserialize the transactions
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                           strprintf("TX decode failed %s", error));
    }

    bool extract = request.params[1].isNull() || (!request.params[1].isNull() &&
                                                  request.params[1].get_bool());

    CMutableTransaction mtx;
    bool complete = FinalizeAndExtractPSBT(psbtx, mtx);

    UniValue result(UniValue::VOBJ);
    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    std::string result_str;

    if (complete && extract) {
        ssTx << mtx;
        result_str = HexStr(ssTx.str());
        result.pushKV("hex", result_str);
    } else {
        ssTx << psbtx;
        result_str = EncodeBase64(ssTx.str());
        result.pushKV("psbt", result_str);
    }
    result.pushKV("complete", complete);

    return result;
}

static UniValue createpsbt(const Config &config,
                           const JSONRPCRequest &request) {
    RPCHelpMan{
        "createpsbt",
        "Creates a transaction in the Partially Signed Transaction format.\n"
        "Implements the Creator role.\n",
        {
            {
                "inputs",
                RPCArg::Type::ARR,
                RPCArg::Optional::NO,
                "A json array of json objects",
                {
                    {
                        "",
                        RPCArg::Type::OBJ,
                        RPCArg::Optional::OMITTED,
                        "",
                        {
                            {"txid", RPCArg::Type::STR_HEX,
                             RPCArg::Optional::NO, "The transaction id"},
                            {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO,
                             "The output number"},
                            {"sequence", RPCArg::Type::NUM, /* default */
                             "depends on the value of the 'locktime' argument",
                             "The sequence number"},
                        },
                    },
                },
            },
            {
                "outputs",
                RPCArg::Type::ARR,
                RPCArg::Optional::NO,
                "a json array with outputs (key-value pairs), where none of "
                "the keys are duplicated.\n"
                "That is, each address can only appear once and there can only "
                "be one 'data' object.\n"
                "For compatibility reasons, a dictionary, which holds the "
                "key-value pairs directly, is also\n"
                "                             accepted as second parameter.",
                {
                    {
                        "",
                        RPCArg::Type::OBJ,
                        RPCArg::Optional::OMITTED,
                        "",
                        {
                            {"address", RPCArg::Type::AMOUNT,
                             RPCArg::Optional::NO,
                             "A key-value pair. The key (string) is the "
                             "bitcoin address, the value (float or string) is "
                             "the amount in " +
                                 CURRENCY_UNIT},
                        },
                    },
                    {
                        "",
                        RPCArg::Type::OBJ,
                        RPCArg::Optional::OMITTED,
                        "",
                        {
                            {"data", RPCArg::Type::STR_HEX,
                             RPCArg::Optional::NO,
                             "A key-value pair. The key must be \"data\", the "
                             "value is hex-encoded data"},
                        },
                    },
                },
            },
            {"locktime", RPCArg::Type::NUM, /* default */ "0",
             "Raw locktime. Non-0 value also locktime-activates inputs"},
        },
        RPCResult{RPCResult::Type::STR, "",
                  "The resulting raw transaction (base64-encoded string)"},
        RPCExamples{HelpExampleCli(
            "createpsbt", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]"
                          "\" \"[{\\\"data\\\":\\\"00010203\\\"}]\"")},
    }
        .Check(request);

    RPCTypeCheck(request.params,
                 {
                     UniValue::VARR,
                     UniValueType(), // ARR or OBJ, checked later
                     UniValue::VNUM,
                 },
                 true);

    CMutableTransaction rawTx =
        ConstructTransaction(config.GetChainParams(), request.params[0],
                             request.params[1], request.params[2]);

    // Make a blank psbt
    PartiallySignedTransaction psbtx;
    psbtx.tx = rawTx;
    for (size_t i = 0; i < rawTx.vin.size(); ++i) {
        psbtx.inputs.push_back(PSBTInput());
    }
    for (size_t i = 0; i < rawTx.vout.size(); ++i) {
        psbtx.outputs.push_back(PSBTOutput());
    }

    // Serialize the PSBT
    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << psbtx;

    return EncodeBase64((uint8_t *)ssTx.data(), ssTx.size());
}

static UniValue converttopsbt(const Config &config,
                              const JSONRPCRequest &request) {
    RPCHelpMan{
        "converttopsbt",
        "Converts a network serialized transaction to a PSBT. "
        "This should be used only with createrawtransaction and "
        "fundrawtransaction\n"
        "createpsbt and walletcreatefundedpsbt should be used for new "
        "applications.\n",
        {
            {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO,
             "The hex string of a raw transaction"},
            {"permitsigdata", RPCArg::Type::BOOL, /* default */ "false",
             "If true, any signatures in the input will be discarded and "
             "conversion.\n"
             "                              will continue. If false, RPC will "
             "fail if any signatures are present."},
        },
        RPCResult{RPCResult::Type::STR, "",
                  "The resulting raw transaction (base64-encoded string)"},
        RPCExamples{
            "\nCreate a transaction\n" +
            HelpExampleCli("createrawtransaction",
                           "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]"
                           "\" \"[{\\\"data\\\":\\\"00010203\\\"}]\"") +
            "\nConvert the transaction to a PSBT\n" +
            HelpExampleCli("converttopsbt", "\"rawtransaction\"")},
    }
        .Check(request);

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VBOOL}, true);

    // parse hex string from parameter
    CMutableTransaction tx;
    bool permitsigdata =
        request.params[1].isNull() ? false : request.params[1].get_bool();
    if (!DecodeHexTx(tx, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    // Remove all scriptSigs from inputs
    for (CTxIn &input : tx.vin) {
        if (!input.scriptSig.empty() && !permitsigdata) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                               "Inputs must not have scriptSigs");
        }
        input.scriptSig.clear();
    }

    // Make a blank psbt
    PartiallySignedTransaction psbtx;
    psbtx.tx = tx;
    for (size_t i = 0; i < tx.vin.size(); ++i) {
        psbtx.inputs.push_back(PSBTInput());
    }
    for (size_t i = 0; i < tx.vout.size(); ++i) {
        psbtx.outputs.push_back(PSBTOutput());
    }

    // Serialize the PSBT
    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << psbtx;

    return EncodeBase64((uint8_t *)ssTx.data(), ssTx.size());
}

#ifdef ENABLE_WALLET

//  currently placeholder to generate big sig ops scripts. currently it's
//  regular script same as createrawtransaction
class CBigSigOpsScriptVisitor : public boost::static_visitor<bool> {
private:
    CScript *script;

public:
    CBigSigOpsScriptVisitor(CScript *scriptin) { script = scriptin; }

    bool operator()(const CNoDestination &dest) const {
        script->clear();
        return false;
    }

    bool operator()(const CKeyID &keyID) const {
        script->clear();
        *script << OP_DUP << OP_HASH160 << ToByteVector(keyID) << OP_EQUALVERIFY
                << OP_CHECKSIG;
        return true;
    }

    bool operator()(const CScriptID &scriptID) const {
        script->clear();
        *script << OP_HASH160 << ToByteVector(scriptID) << OP_EQUAL;
        return true;
    }
};

CScript GetBigSigOpsScriptForDestination(const CTxDestination &dest) {
    CScript script;

    boost::apply_visitor(CBigSigOpsScriptVisitor(&script), dest);
    return script;
}

class ProgressLogHelper {
public:
    ProgressLogHelper(uint32_t t, std::string l = "operations")
        : total(t), percent(0), success(false), label(l) {
        LogPrintf("%s start\n", label.c_str());
    }

    ~ProgressLogHelper() {
        if (success)
            LogPrintf("%s done\n", label.c_str());
        else
            LogPrintf("%s stopped\n", label.c_str());
    }

    void PrintProgress(uint32_t count) {
        int newPercent = count * 100 / total;
        if (newPercent > percent) {
            percent = newPercent;
            LogPrintf("%s progress %d%% (%d/%d)\n", label.c_str(), percent,
                      count, total);
        }
    }

    uint32_t total;
    int percent;
    bool success;
    std::string label;
};

static UniValue fillmempool(const Config &config,
                            const JSONRPCRequest &request) {
    CWallet *const pwallet = GetWalletForJSONRPCRequest(request);
    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() > 2) {
        throw std::runtime_error(
            "fillmempool\n"
            "Create random transaction\n "
            "1. number of target address per transaction\n "
            "2. maximum transaction count\n "
            "Returns array of transaction ids\n");
    }

    int OUTPUT_PER_INPUT = 10;
    if (request.params.size() > 0) {
        if (request.params[0].isNum()) {
            OUTPUT_PER_INPUT = request.params[0].get_int();
            if (OUTPUT_PER_INPUT < 1) OUTPUT_PER_INPUT = 1;
        } else {
            LogPrintf("Passing non-integer param. value: %s",
                      request.params[0].get_str().c_str());
        }
    }

    int maxTxSize = MAX_TX_SIZE;
    if (request.params.size() > 1) {
        if (request.params[1].isNum()) {
            maxTxSize = request.params[1].get_int();
            if (maxTxSize < 1) maxTxSize = 1;
        } else {
            LogPrintf("Passing non-integer param. value: %s",
                      request.params[1].get_str().c_str());
        }
    }

    // Parse the account first so we don't generate a key if there's an error
    std::string strAccount;
    if (!pwallet->IsLocked()) {
        pwallet->TopUpKeyPool();
    }
    LOCK2(cs_main, pwallet->cs_wallet);
    //  =========== get list unspent ====================//

    struct Unspent {
        std::string txid;
        uint32_t vout;
        int64_t satoshis;
    };

    std::vector<Unspent> unspentList;
    {
        bool include_unsafe = true;
        std::vector<COutput> vecOutputs;
        assert(pwallet != nullptr);
        pwallet->AvailableCoins(vecOutputs, !include_unsafe, nullptr);
        for (const COutput &out : vecOutputs) {
            CTxDestination address;
            const CScript &scriptPubKey = out.tx->tx->vout[out.i].scriptPubKey;
            bool fValidAddress = ExtractDestination(scriptPubKey, address);

            if (!fValidAddress) continue;

            const Amount &amount = out.tx->tx->vout[out.i].nValue;
            unspentList.push_back(Unspent{out.tx->GetId().GetHex(),
                                          static_cast<uint32_t>(out.i),
                                          amount / SATOSHI});
        }
    }
    LogPrintf("Found %d unspent transactions\n", unspentList.size());
    //  =========== get new address =====================//

    // Generate a new key that is added to wallet
    std::vector<std::string> addresses;
    {
        int totalOut =
            OUTPUT_PER_INPUT; // unspentList.size() * OUTPUT_PER_INPUT; //  send
                              // to 10 address per input
        ProgressLogHelper a(totalOut, "get new address");
        for (int i = 0; i < totalOut; ++i) {
            CPubKey newKey;
            if (!pwallet->GetKeyFromPool(newKey)) {
                throw JSONRPCError(
                    RPC_WALLET_KEYPOOL_RAN_OUT,
                    "Error: Keypool ran out, please call keypoolrefill first");
            }
            CKeyID keyID = newKey.GetID();

            pwallet->SetAddressBook(keyID, strAccount, "receive");
            addresses.push_back(EncodeDestination(keyID));
            a.PrintProgress(i);
        }
    }

    //  ==================== createrawtransaction ===========================//
    std::vector<CMutableTransaction> rawHxTxs;
    {
        // int startingOutAddress = 0;
        unsigned int totalTxs =
            std::min((unsigned int)maxTxSize, (unsigned int)unspentList.size());
        rawHxTxs.reserve(totalTxs);
        ProgressLogHelper a(totalTxs, "Create raw transaction");

        unsigned int startingUnspentIdx = 0;
        CFeeRate minRelayTxFee = config.GetMinFeePerKB();
        Amount feePerK = minRelayTxFee.GetFeePerK();
        const int assumedTxoutPerKb = 20;
        int64_t relayFeePerTxout =
            std::max((int64_t)200,
                     OUTPUT_PER_INPUT * feePerK / assumedTxoutPerKb / SATOSHI);

        while (startingUnspentIdx < unspentList.size() &&
               rawHxTxs.size() < totalTxs) {
            int64_t satoshisPerDest = -1;
            int64_t totalUnspent = 0;
            int unspentCount = 0;
            while (satoshisPerDest < 10000 &&
                   startingUnspentIdx + unspentCount < unspentList.size()) {
                int currIdx = startingUnspentIdx + unspentCount;
                auto &unspent = unspentList[currIdx];
                totalUnspent += unspent.satoshis;
                satoshisPerDest =
                    (totalUnspent / OUTPUT_PER_INPUT) - relayFeePerTxout;
                ++unspentCount;
            }

            if (satoshisPerDest < 10000) break;
            // LogPrintf( "Create raw transaction - satoshisPerDest: %ld\n",
            // satoshisPerDest );

            CMutableTransaction rawTx;
            for (int i = 0; i < unspentCount; ++i) {
                int currIdx = startingUnspentIdx + i;
                auto &unspent = unspentList[currIdx];
                uint256 txid;
                txid.SetHex(unspent.txid);
                CTxIn in(COutPoint(txid, unspent.vout), CScript(),
                         std::numeric_limits<uint32_t>::max());
                rawTx.vin.push_back(in);
            }

            Amount nAmount = satoshisPerDest * SATOSHI;

            std::set<CTxDestination> destinations;
            // int endOutput = startingOutAddress + OUTPUT_PER_INPUT;
            for (int i = 0; i < OUTPUT_PER_INPUT; ++i) {
                const auto &name_ = addresses[i];
                CTxDestination destination =
                    DecodeDestination(name_, config.GetChainParams());
                if (!IsValidDestination(destination)) {
                    throw JSONRPCError(
                        RPC_INVALID_ADDRESS_OR_KEY,
                        std::string("Invalid Bitcoin address: ") + name_);
                }

                if (!destinations.insert(destination).second) {
                    throw JSONRPCError(
                        RPC_INVALID_PARAMETER,
                        std::string("Invalid parameter, duplicated address: ") +
                            name_);
                }

                CScript scriptPubKey =
                    GetBigSigOpsScriptForDestination(destination);

                CTxOut out(nAmount, scriptPubKey);
                rawTx.vout.push_back(out);
            }

            rawHxTxs.push_back(rawTx);
            startingUnspentIdx += unspentCount;
            a.PrintProgress(startingUnspentIdx);
        }
    }

    //  ======================= Sign transactions
    //  =================================//
    LogPrintf("Signing transactions\n");
    {
        int counter = 0;
        const CKeyStore &keystore = *pwallet;
        SigHashType sigHashType = SigHashType().withForkId();
        ProgressLogHelper a(rawHxTxs.size(), "Signing transactions");

        for (CMutableTransaction &tx : rawHxTxs) {
            CCoinsView viewDummy;
            CCoinsViewCache view(&viewDummy);
            {
                LOCK(g_mempool.cs);
                CCoinsViewCache &viewChain = *pcoinsTip;
                CCoinsViewMemPool viewMempool(&viewChain, g_mempool);
                // Temporarily switch cache backend to db+mempool view.
                view.SetBackend(viewMempool);

                for (const CTxIn &txin : tx.vin) {
                    // Load entries from viewChain into view; can fail.
                    view.AccessCoin(txin.prevout);
                }

                // Switch back to avoid locking mempool for too long.
                view.SetBackend(viewDummy);
            }

            const CTransaction txConst(tx);

            UniValue vErrors(UniValue::VARR);
            for (size_t i = 0; i < tx.vin.size(); i++) {
                CTxIn &txin = tx.vin[i];
                const Coin &coin = view.AccessCoin(txin.prevout);
                if (coin.IsSpent()) {
                    TxInErrorToJSON(txin, vErrors,
                                    "Input not found or already spent");
                    continue;
                }

                const CScript &prevPubKey = coin.GetTxOut().scriptPubKey;
                const Amount amount = coin.GetTxOut().nValue;

                SignatureData sigdata;
                // Only sign SIGHASH_SINGLE if there's a corresponding output:
                if ((sigHashType.getBaseType() != BaseSigHashType::SINGLE) ||
                    (i < tx.vout.size())) {
                    ProduceSignature(
                        MutableTransactionSignatureCreator(&keystore, &tx, i,
                                                           amount, sigHashType),
                        prevPubKey, sigdata);
                }

                UpdateTransaction(tx, i, sigdata);

                ScriptError serror = SCRIPT_ERR_OK;
                if (!VerifyScript(
                        txin.scriptSig, prevPubKey,
                        STANDARD_SCRIPT_VERIFY_FLAGS,
                        TransactionSignatureChecker(&txConst, i, amount),
                        &serror)) {
                    TxInErrorToJSON(txin, vErrors, ScriptErrorString(serror));
                }
            }
            ++counter;
            a.PrintProgress(counter);
        }
        a.success = true;
    }

    UniValue result(UniValue::VARR);
    Amount nMaxRawTxFee = maxTxFee;
    //  ================================ send transaction
    //  ==================================//
    {
        ProgressLogHelper a(rawHxTxs.size(), "Submitting transactions");

        int count = 0;
        for (CMutableTransaction &mtx : rawHxTxs) {
            CTransactionRef tx(MakeTransactionRef(std::move(mtx)));
            const uint256 &txid = tx->GetId();

            CValidationState state;
            bool fLimitFree = false;
            bool fMissingInputs = false;
            if (!AcceptToMemoryPool(config, g_mempool, state, std::move(tx),
                                    fLimitFree, &fMissingInputs, false,
                                    nMaxRawTxFee)) {
                if (state.IsInvalid()) {
                    throw JSONRPCError(RPC_TRANSACTION_REJECTED,
                                       strprintf("%i: %s",
                                                 state.GetRejectCode(),
                                                 state.GetRejectReason()));
                } else {
                    if (fMissingInputs) {
                        throw JSONRPCError(RPC_TRANSACTION_ERROR,
                                           "Missing inputs");
                    }

                    throw JSONRPCError(RPC_TRANSACTION_ERROR,
                                       state.GetRejectReason());
                }
            }

            result.push_back(txid.GetHex());
            CInv inv(MSG_TX, txid);
            g_connman->ForEachNode(
                [&inv](CNode *pnode) { pnode->PushInventory(inv); });
            ++count;
            a.PrintProgress(count);
        }
        a.success = true;
    }

    return result;
}

#endif //   ENABLE_WALLET

// clang-format off
static const CRPCCommand commands[] = {
    //  category            name                         actor (function)           argNames
    //  ------------------- ------------------------     ----------------------     ----------
    { "rawtransactions",    "getrawtransaction",         getrawtransaction,         {"txid","verbose","blockhash"} },
    { "rawtransactions",    "createrawtransaction",      createrawtransaction,      {"inputs","outputs","locktime"} },
    { "rawtransactions",    "decoderawtransaction",      decoderawtransaction,      {"hexstring"} },
    { "rawtransactions",    "decodescript",              decodescript,              {"hexstring"} },
    { "rawtransactions",    "sendrawtransaction",        sendrawtransaction,        {"hexstring","allowhighfees|maxfeerate"} },
    { "rawtransactions",    "combinerawtransaction",     combinerawtransaction,     {"txs"} },
    { "rawtransactions",    "signrawtransactionwithkey", signrawtransactionwithkey, {"hexstring","privkeys","prevtxs","sighashtype"} },
    { "rawtransactions",    "testmempoolaccept",         testmempoolaccept,         {"rawtxs","allowhighfees|maxfeerate"} },
    { "rawtransactions",    "decodepsbt",                decodepsbt,                {"psbt"} },
    { "rawtransactions",    "combinepsbt",               combinepsbt,               {"txs"} },
    { "rawtransactions",    "finalizepsbt",              finalizepsbt,              {"psbt", "extract"} },
    { "rawtransactions",    "createpsbt",                createpsbt,                {"inputs","outputs","locktime"} },
    { "rawtransactions",    "converttopsbt",             converttopsbt,             {"hexstring","permitsigdata"} },

#ifdef ENABLE_WALLET
    { "rawtransactions",    "fillmempool",               fillmempool,               {"outputcount"} }, 
#endif
    { "blockchain",         "gettxoutproof",             gettxoutproof,             {"txids", "blockhash"} },
    { "blockchain",         "verifytxoutproof",          verifytxoutproof,          {"proof"} },
};
// clang-format on

void RegisterRawTransactionRPCCommands(CRPCTable &t) {
    for (unsigned int vcidx = 0; vcidx < ARRAYLEN(commands); vcidx++) {
        t.appendCommand(commands[vcidx].name, &commands[vcidx]);
    }
}
