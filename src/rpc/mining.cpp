// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "consensus/activation.h"
#include <amount.h>
#include <blockvalidity.h>
#include <cashaddrenc.h>
#include <chain.h>
#include <chainparams.h>
#include <config.h>
#include <consensus/activation.h>
#include <consensus/consensus.h>
#include <consensus/params.h>
#include <consensus/validation.h>
#include <core_io.h>
#include <key_io.h>
#include <miner.h>
#include <minerfund.h>
#include <net.h>
#include <node/context.h>
#include <policy/policy.h>
#include <pow/pow.h>
#include <rpc/blockchain.h>
#include <rpc/server.h>
#include <rpc/util.h>
#include <script/descriptor.h>
#include <script/script.h>
#include <shutdown.h>
#include <txmempool.h>
#include <univalue.h>
#include <util/strencodings.h>
#include <util/system.h>
#include <validation.h>
#include <validationinterface.h>
#include <warnings.h>

#include <cstdint>

#include <fs.h>

std::unordered_map<std::string, std::vector<CTransactionRef>>
    gGetblocktemplatelightCacheMap; //  keep the transactions based on the
                                    //  job_id
std::vector<std::string> gGetblocktemplatelightIdList; //  keep the job_id order
CCriticalSection cs_getblocktemplatelight;

/**
 * Return average network hashes per second based on the last 'lookup' blocks,
 * or from the last difficulty change if 'lookup' is nonpositive. If 'height' is
 * nonnegative, compute the estimate at the time when a given block was found.
 */
static UniValue GetNetworkHashPS(int lookup, int height) {
    CBlockIndex *pb = ::ChainActive().Tip();

    if (height >= 0 && height < ::ChainActive().Height()) {
        pb = ::ChainActive()[height];
    }

    if (pb == nullptr || !pb->nHeight) {
        return 0;
    }

    // If lookup is -1, then use blocks since last difficulty change.
    if (lookup <= 0) {
        lookup = pb->nHeight %
                     Params().GetConsensus().DifficultyAdjustmentInterval() +
                 1;
    }

    // If lookup is larger than chain, then set it to chain length.
    if (lookup > pb->nHeight) {
        lookup = pb->nHeight;
    }

    CBlockIndex *pb0 = pb;
    int64_t minTime = pb0->GetBlockTime();
    int64_t maxTime = minTime;
    for (int i = 0; i < lookup; i++) {
        pb0 = pb0->pprev;
        int64_t time = pb0->GetBlockTime();
        minTime = std::min(time, minTime);
        maxTime = std::max(time, maxTime);
    }

    // In case there's a situation where minTime == maxTime, we don't want a
    // divide by zero exception.
    if (minTime == maxTime) {
        return 0;
    }

    arith_uint256 workDiff = pb->nChainWork - pb0->nChainWork;
    int64_t timeDiff = maxTime - minTime;

    return workDiff.getdouble() / timeDiff;
}

static UniValue getnetworkhashps(const Config &config,
                                 const JSONRPCRequest &request) {
    RPCHelpMan{
        "getnetworkhashps",
        "Returns the estimated network hashes per second based on the last n "
        "blocks.\n"
        "Pass in [blocks] to override # of blocks, -1 specifies since last "
        "difficulty change.\n"
        "Pass in [height] to estimate the network speed at the time when a "
        "certain block was found.\n",
        {
            {"nblocks", RPCArg::Type::NUM, /* default */ "120",
             "The number of blocks, or -1 for blocks since last difficulty "
             "change."},
            {"height", RPCArg::Type::NUM, /* default */ "-1",
             "To estimate at the time of the given height."},
        },
        RPCResult{RPCResult::Type::NUM, "", "Hashes per second estimated"},
        RPCExamples{HelpExampleCli("getnetworkhashps", "") +
                    HelpExampleRpc("getnetworkhashps", "")},
    }
        .Check(request);

    LOCK(cs_main);
    return GetNetworkHashPS(
        !request.params[0].isNull() ? request.params[0].get_int() : 120,
        !request.params[1].isNull() ? request.params[1].get_int() : -1);
}

static UniValue generateBlocks(const Config &config, const CTxMemPool &mempool,
                               const CScript &coinbase_script, int nGenerate,
                               uint64_t nMaxTries) {
    int nHeightEnd = 0;
    int nHeight = 0;

    {
        // Don't keep cs_main locked.
        LOCK(cs_main);
        nHeight = ::ChainActive().Height();
        nHeightEnd = nHeight + nGenerate;
    }

    const uint64_t nExcessiveBlockSize = config.GetMaxBlockSize();

    unsigned int nExtraNonce = 0;
    UniValue blockHashes(UniValue::VARR);
    while (nHeight < nHeightEnd && !ShutdownRequested()) {
        std::unique_ptr<CBlockTemplate> pblocktemplate(
            BlockAssembler(config, mempool).CreateNewBlock(coinbase_script));

        if (!pblocktemplate.get()) {
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Couldn't create new block");
        }

        CBlock *pblock = &pblocktemplate->block;

        {
            LOCK(cs_main);
            IncrementExtraNonce(pblock, ::ChainActive().Tip(),
                                nExcessiveBlockSize, nExtraNonce);
        }

        while (nMaxTries > 0 &&
               pblock->nNonce < std::numeric_limits<uint32_t>::max() &&
               !CheckProofOfWork(pblock->GetHash(), pblock->nBits,
                                 config.GetChainParams().GetConsensus()) &&
               !ShutdownRequested()) {
            ++pblock->nNonce;
            --nMaxTries;
        }

        if (nMaxTries == 0 || ShutdownRequested()) {
            break;
        }

        if (pblock->nNonce == std::numeric_limits<uint32_t>::max()) {
            continue;
        }

        std::shared_ptr<const CBlock> shared_pblock =
            std::make_shared<const CBlock>(*pblock);
        if (!ProcessNewBlock(config, shared_pblock, true, nullptr)) {
            throw JSONRPCError(RPC_INTERNAL_ERROR,
                               "ProcessNewBlock, block not accepted");
        }
        ++nHeight;
        blockHashes.push_back(pblock->GetHash().GetHex());
    }

    return blockHashes;
}

static UniValue generatetodescriptor(const Config &config,
                                     const JSONRPCRequest &request) {
    RPCHelpMan{
        "generatetodescriptor",
        "\nMine blocks immediately to a specified descriptor (before the RPC "
        "call returns)\n",
        {
            {"num_blocks", RPCArg::Type::NUM, RPCArg::Optional::NO,
             "How many blocks are generated immediately."},
            {"descriptor", RPCArg::Type::STR, RPCArg::Optional::NO,
             "The descriptor to send the newly generated bitcoin to."},
            {"maxtries", RPCArg::Type::NUM, /* default */ "1000000",
             "How many iterations to try."},
        },
        RPCResult{RPCResult::Type::ARR,
                  "",
                  "hashes of blocks generated",
                  {
                      {RPCResult::Type::STR_HEX, "", "blockhash"},
                  }},
        RPCExamples{"\nGenerate 11 blocks to mydesc\n" +
                    HelpExampleCli("generatetodescriptor", "11 \"mydesc\"")},
    }
        .Check(request);

    const int num_blocks{request.params[0].get_int()};
    const int64_t max_tries{
        request.params[2].isNull() ? 1000000 : request.params[2].get_int()};

    FlatSigningProvider key_provider;
    std::string error;
    const auto desc = Parse(request.params[1].get_str(), key_provider, error,
                            /* require_checksum = */ false);
    if (!desc) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, error);
    }
    if (desc->IsRange()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER,
                           "Ranged descriptor not accepted. Maybe pass through "
                           "deriveaddresses first?");
    }

    FlatSigningProvider provider;
    std::vector<CScript> coinbase_script;
    if (!desc->Expand(0, key_provider, coinbase_script, provider)) {
        throw JSONRPCError(
            RPC_INVALID_ADDRESS_OR_KEY,
            strprintf("Cannot derive script without private keys"));
    }

    const CTxMemPool &mempool = EnsureMemPool(request.context);

    CHECK_NONFATAL(coinbase_script.size() == 1);

    return generateBlocks(config, mempool, coinbase_script.at(0), num_blocks,
                          max_tries);
}

static UniValue generatetoaddress(const Config &config,
                                  const JSONRPCRequest &request) {
    RPCHelpMan{
        "generatetoaddress",
        "Mine blocks immediately to a specified address before the "
        "RPC call returns)\n",
        {
            {"nblocks", RPCArg::Type::NUM, RPCArg::Optional::NO,
             "How many blocks are generated immediately."},
            {"address", RPCArg::Type::STR, RPCArg::Optional::NO,
             "The address to send the newly generated bitcoin to."},
            {"maxtries", RPCArg::Type::NUM, /* default */ "1000000",
             "How many iterations to try."},
        },
        RPCResult{RPCResult::Type::ARR,
                  "",
                  "hashes of blocks generated",
                  {
                      {RPCResult::Type::STR_HEX, "", "blockhash"},
                  }},
        RPCExamples{
            "\nGenerate 11 blocks to myaddress\n" +
            HelpExampleCli("generatetoaddress", "11 \"myaddress\"") +
            "If you are running the Bitcoin ABC wallet, you can get a new "
            "address to send the newly generated bitcoin to with:\n" +
            HelpExampleCli("getnewaddress", "")},
    }
        .Check(request);

    int nGenerate = request.params[0].get_int();
    uint64_t nMaxTries = 1000000;
    if (!request.params[2].isNull()) {
        nMaxTries = request.params[2].get_int64();
    }

    CTxDestination destination =
        DecodeDestination(request.params[1].get_str(), config.GetChainParams());
    if (!IsValidDestination(destination)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY,
                           "Error: Invalid address");
    }

    const CTxMemPool &mempool = EnsureMemPool(request.context);

    CScript coinbase_script = GetScriptForDestination(destination);

    return generateBlocks(config, mempool, coinbase_script, nGenerate,
                          nMaxTries);
}

static UniValue getmininginfo(const Config &config,
                              const JSONRPCRequest &request) {
    RPCHelpMan{
        "getmininginfo",
        "Returns a json object containing mining-related "
        "information.",
        {},
        RPCResult{
            RPCResult::Type::OBJ,
            "",
            "",
            {
                {RPCResult::Type::NUM, "blocks", "The current block"},
                {RPCResult::Type::NUM, "currentblocksize", /* optional */ true,
                 "The block size of the last assembled block (only present if "
                 "a block was ever assembled)"},
                {RPCResult::Type::NUM, "currentblocktx", /* optional */ true,
                 "The number of block transactions of the last assembled block "
                 "(only present if a block was ever assembled)"},
                {RPCResult::Type::NUM, "difficulty", "The current difficulty"},
                {RPCResult::Type::NUM, "networkhashps",
                 "The network hashes per second"},
                {RPCResult::Type::NUM, "pooledtx", "The size of the mempool"},
                {RPCResult::Type::STR, "chain",
                 "current network name (main, test, regtest)"},
                {RPCResult::Type::STR, "warnings",
                 "any network and blockchain warnings"},
            }},
        RPCExamples{HelpExampleCli("getmininginfo", "") +
                    HelpExampleRpc("getmininginfo", "")},
    }
        .Check(request);

    LOCK(cs_main);
    const CTxMemPool &mempool = EnsureMemPool(request.context);

    UniValue obj(UniValue::VOBJ);
    obj.pushKV("blocks", int(::ChainActive().Height()));
    if (BlockAssembler::m_last_block_size) {
        obj.pushKV("currentblocksize", *BlockAssembler::m_last_block_size);
    }
    if (BlockAssembler::m_last_block_num_txs) {
        obj.pushKV("currentblocktx", *BlockAssembler::m_last_block_num_txs);
    }
    obj.pushKV("difficulty", double(GetDifficulty(::ChainActive().Tip())));
    obj.pushKV("networkhashps", getnetworkhashps(config, request));
    obj.pushKV("pooledtx", uint64_t(mempool.size()));
    obj.pushKV("chain", config.GetChainParams().NetworkIDString());
    obj.pushKV("warnings", GetWarnings(false));

    return obj;
}

// NOTE: Unlike wallet RPC (which use BCH values), mining RPCs follow GBT (BIP
// 22) in using satoshi amounts
static UniValue prioritisetransaction(const Config &config,
                                      const JSONRPCRequest &request) {
    RPCHelpMan{
        "prioritisetransaction",
        "Accepts the transaction into mined blocks at a higher "
        "(or lower) priority\n",
        {
            {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO,
             "The transaction id."},
            {"dummy", RPCArg::Type::NUM, RPCArg::Optional::OMITTED_NAMED_ARG,
             "API-Compatibility for previous API. Must be zero or null.\n"
             "                  DEPRECATED. For forward compatibility "
             "use named arguments and omit this parameter."},
            {"fee_delta", RPCArg::Type::NUM, RPCArg::Optional::NO,
             "The fee value (in satoshis) to add (or subtract, if negative).\n"
             "                        The fee is not actually paid, only the "
             "algorithm for selecting transactions into a block\n"
             "                  considers the transaction as it would "
             "have paid a higher (or lower) fee."},
        },
        RPCResult{RPCResult::Type::BOOL, "", "Returns true"},
        RPCExamples{
            HelpExampleCli("prioritisetransaction", "\"txid\" 0.0 10000") +
            HelpExampleRpc("prioritisetransaction", "\"txid\", 0.0, 10000")},
    }
        .Check(request);

    LOCK(cs_main);

    TxId txid(ParseHashV(request.params[0], "txid"));
    Amount nAmount = request.params[2].get_int64() * SATOSHI;

    if (!(request.params[1].isNull() || request.params[1].get_real() == 0)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER,
                           "Priority is no longer supported, dummy argument to "
                           "prioritisetransaction must be 0.");
    }

    EnsureMemPool(request.context).PrioritiseTransaction(txid, nAmount);
    return true;
}

// NOTE: Assumes a conclusive result; if result is inconclusive, it must be
// handled by caller
static UniValue BIP22ValidationResult(const Config &config,
                                      const BlockValidationState &state) {
    if (state.IsValid()) {
        return NullUniValue;
    }

    if (state.IsError()) {
        throw JSONRPCError(RPC_VERIFY_ERROR, state.ToString());
    }

    if (state.IsInvalid()) {
        std::string strRejectReason = state.GetRejectReason();
        if (strRejectReason.empty()) {
            return "rejected";
        }
        return strRejectReason;
    }

    // Should be impossible.
    return "valid?";
}

static void makeMerkleBranch(const std::vector<uint256> &vtxhashs,
                             std::vector<uint256> &steps) {
    if (vtxhashs.size() == 0) {
        return;
    }
    std::vector<uint256> hashs(vtxhashs.begin(), vtxhashs.end());
    while (hashs.size() > 1) {
        // put first element
        steps.push_back(*hashs.begin());
        if (hashs.size() % 2 == 0) {
            // if even, push_back the end one, size should be an odd number.
            // because we ignore the coinbase tx when make merkle branch.
            hashs.push_back(*hashs.rbegin());
        }
        // ignore the first one than merge two
        for (size_t i = 0; i < (hashs.size() - 1) / 2; i++) {
            // Hash = Double SHA256
            hashs[i] = Hash(BEGIN(hashs[i * 2 + 1]), END(hashs[i * 2 + 1]),
                            BEGIN(hashs[i * 2 + 2]), END(hashs[i * 2 + 2]));
        }
        hashs.resize((hashs.size() - 1) / 2);
    }
    assert(hashs.size() == 1);
    steps.push_back(*hashs.begin()); // put the last one
}

static UniValue getblocktemplatecommon(bool lightVersion, const Config &config,
                                       const JSONRPCRequest &request) {
    bool wrongParamSize =
        lightVersion ? request.params.size() > 2 : request.params.size() > 1;
    if (request.fHelp || wrongParamSize) {
        throw std::runtime_error(
            "getblocktemplate ( TemplateRequest )\n"
            "\nIf the request parameters include a 'mode' key, that is used to "
            "explicitly select between the default 'template' request or a "
            "'proposal'.\n"
            "It returns data needed to construct a block to work on.\n"
            "For full specification, see BIPs 22, 23, 9, and 145:\n"
            "    "
            "https://github.com/bitcoin/bips/blob/master/bip-0022.mediawiki\n"
            "    "
            "https://github.com/bitcoin/bips/blob/master/bip-0023.mediawiki\n"
            "    "
            "https://github.com/bitcoin/bips/blob/master/"
            "bip-0009.mediawiki#getblocktemplate_changes\n"
            "    "
            "https://github.com/bitcoin/bips/blob/master/bip-0145.mediawiki\n"

            "\nArguments:\n"
            "1. template_request         (json object, optional) A json object "
            "in the following spec\n"
            "     {\n"
            "       \"mode\":\"template\"    (string, optional) This must be "
            "set to \"template\", \"proposal\" (see BIP 23), or omitted\n"
            "       \"capabilities\":[     (array, optional) A list of "
            "strings\n"
            "           \"support\"          (string) client side supported "
            "feature, 'longpoll', 'coinbasetxn', 'coinbasevalue', 'proposal', "
            "'serverlist', 'workid'\n"
            "           ,...\n"
            "       ]\n"
            "     }\n"
            "\n"

            "\nResult:\n"
            "{\n"
            "  \"version\" : n,                    (numeric) The preferred "
            "block version\n"
            "  \"previousblockhash\" : \"xxxx\",     (string) The hash of "
            "current highest block\n"
            "  \"transactions\" : [                (array) contents of "
            "non-coinbase transactions that should be included in the next "
            "block\n"
            "      {\n"
            "         \"data\" : \"xxxx\",             (string) transaction "
            "data encoded in hexadecimal (byte-for-byte)\n"
            "         \"txid\" : \"xxxx\",             (string) transaction id "
            "encoded in little-endian hexadecimal\n"
            "         \"hash\" : \"xxxx\",             (string) hash encoded "
            "in little-endian hexadecimal (including witness data)\n"
            "         \"depends\" : [                (array) array of numbers "
            "\n"
            "             n                          (numeric) transactions "
            "before this one (by 1-based index in 'transactions' list) that "
            "must be present in the final block if this one is\n"
            "             ,...\n"
            "         ],\n"
            "         \"fee\": n,                    (numeric) difference in "
            "value between transaction inputs and outputs (in satoshis); for "
            "coinbase transactions, this is a negative Number of the total "
            "collected block fees (ie, not including the block subsidy); if "
            "key is not present, fee is unknown and clients MUST NOT assume "
            "there isn't one\n"
            "         \"sigops\" : n,                (numeric) total SigOps "
            "cost, as counted for purposes of block limits; if key is not "
            "present, sigop cost is unknown and clients MUST NOT assume it is "
            "zero\n"
            "         \"required\" : true|false      (boolean) if provided and "
            "true, this transaction must be in the final block\n"
            "      }\n"
            "      ,...\n"
            "  ],\n"
            "  \"coinbaseaux\" : {                 (json object) data that "
            "should be included in the coinbase's scriptSig content\n"
            "      \"flags\" : \"xx\"                  (string) key name is to "
            "be ignored, and value included in scriptSig\n"
            "  },\n"
            "  \"coinbasevalue\" : n,              (numeric) maximum allowable "
            "input to coinbase transaction, including the generation award and "
            "transaction fees (in satoshis)\n"
            "  \"coinbasetxn\" : { ... },          (json object) information "
            "for coinbase transaction\n"
            "  \"target\" : \"xxxx\",                (string) The hash target\n"
            "  \"mintime\" : xxx,                  (numeric) The minimum "
            "timestamp appropriate for next block time in seconds since epoch "
            "(Jan 1 1970 GMT)\n"
            "  \"mutable\" : [                     (array of string) list of "
            "ways the block template may be changed \n"
            "     \"value\"                          (string) A way the block "
            "template may be changed, e.g. 'time', 'transactions', "
            "'prevblock'\n"
            "     ,...\n"
            "  ],\n"
            "  \"noncerange\" : \"00000000ffffffff\",(string) A range of valid "
            "nonces\n"
            "  \"sigoplimit\" : n,                 (numeric) limit of sigops "
            "in blocks\n"
            "  \"sizelimit\" : n,                  (numeric) limit of block "
            "size\n"
            "  \"curtime\" : ttt,                  (numeric) current timestamp "
            "in seconds since epoch (Jan 1 1970 GMT)\n"
            "  \"bits\" : \"xxxxxxxx\",              (string) compressed "
            "target of next block\n"
            "  \"height\" : n                      (numeric) The height of the "
            "next block\n"
            "}\n"

            "\nExamples:\n" +
            HelpExampleCli("getblocktemplate", "") +
            HelpExampleRpc("getblocktemplate", ""));
    }

    LOCK(cs_main);
    const CChainParams &chainparams = config.GetChainParams();

    std::string strMode = "template";
    UniValue lpval = NullUniValue;
    std::set<std::string> setClientRules;
    if (!request.params[0].isNull()) {
        const UniValue &oparam = request.params[0].get_obj();
        const UniValue &modeval = find_value(oparam, "mode");
        if (modeval.isStr()) {
            strMode = modeval.get_str();
        } else if (modeval.isNull()) {
            /* Do nothing */
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid mode");
        }
        lpval = find_value(oparam, "longpollid");

        if (strMode == "proposal") {
            const UniValue &dataval = find_value(oparam, "data");
            if (!dataval.isStr()) {
                throw JSONRPCError(RPC_TYPE_ERROR,
                                   "Missing data String key for proposal");
            }

            CBlock block;
            if (!DecodeHexBlk(block, dataval.get_str())) {
                throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                                   "Block decode failed");
            }

            const BlockHash hash = block.GetHash();
            const CBlockIndex *pindex = LookupBlockIndex(hash);
            if (pindex) {
                if (pindex->IsValid(BlockValidity::SCRIPTS)) {
                    return "duplicate";
                }
                if (pindex->nStatus.isInvalid()) {
                    return "duplicate-invalid";
                }
                return "duplicate-inconclusive";
            }

            CBlockIndex *const pindexPrev = ::ChainActive().Tip();
            // TestBlockValidity only supports blocks built on the current Tip
            if (block.hashPrevBlock != pindexPrev->GetBlockHash()) {
                return "inconclusive-not-best-prevblk";
            }
            BlockValidationState state;
            TestBlockValidity(state, chainparams, block, pindexPrev,
                              BlockValidationOptions(config)
                                  .withCheckPoW(false)
                                  .withCheckMerkleRoot(true));
            return BIP22ValidationResult(config, state);
        }
    }

    //  GBTLight only. BTC.COM specific. Inject transactions to be added in the
    //  block
    std::vector<CMutableTransaction> injectTxs;
    if (lightVersion && request.params.size() > 1) {
        const UniValue &injectedTxsHex = request.params[1].get_array();
        injectTxs.reserve(injectedTxsHex.size());
        for (unsigned int idx = 0; idx < injectedTxsHex.size(); idx++) {
            CMutableTransaction tx;
            if (DecodeHexTx(tx, injectedTxsHex[idx].get_str())) {
                injectTxs.push_back(std::move(tx));
            }
        }
    }

    if (strMode != "template") {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid mode");
    }

    NodeContext &node = EnsureNodeContext(request.context);
    if (!node.connman) {
        throw JSONRPCError(
            RPC_CLIENT_P2P_DISABLED,
            "Error: Peer-to-peer functionality missing or disabled");
    }

    if (node.connman->GetNodeCount(CConnman::CONNECTIONS_ALL) == 0) {
        throw JSONRPCError(RPC_CLIENT_NOT_CONNECTED,
                           "Bitcoin is not connected!");
    }

    if (::ChainstateActive().IsInitialBlockDownload()) {
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, PACKAGE_NAME
                           " is in initial sync and waiting for blocks...");
    }

    static unsigned int nTransactionsUpdatedLast;
    const CTxMemPool &mempool = EnsureMemPool(request.context);

    if (!lpval.isNull()) {
        // Wait to respond until either the best block changes, OR a minute has
        // passed and there are more transactions
        uint256 hashWatchedChain;
        std::chrono::steady_clock::time_point checktxtime;
        unsigned int nTransactionsUpdatedLastLP;

        if (lpval.isStr()) {
            // Format: <hashBestChain><nTransactionsUpdatedLast>
            std::string lpstr = lpval.get_str();

            hashWatchedChain = ParseHashV(lpstr.substr(0, 64), "longpollid");
            nTransactionsUpdatedLastLP = atoi64(lpstr.substr(64));
        } else {
            // NOTE: Spec does not specify behaviour for non-string longpollid,
            // but this makes testing easier
            hashWatchedChain = ::ChainActive().Tip()->GetBlockHash();
            nTransactionsUpdatedLastLP = nTransactionsUpdatedLast;
        }

        // Release lock while waiting
        LEAVE_CRITICAL_SECTION(cs_main);
        {
            checktxtime =
                std::chrono::steady_clock::now() + std::chrono::minutes(1);

            WAIT_LOCK(g_best_block_mutex, lock);
            while (g_best_block == hashWatchedChain && IsRPCRunning()) {
                if (g_best_block_cv.wait_until(lock, checktxtime) ==
                    std::cv_status::timeout) {
                    // Timeout: Check transactions for update
                    // without holding the mempool look to avoid deadlocks
                    if (mempool.GetTransactionsUpdated() !=
                        nTransactionsUpdatedLastLP) {
                        break;
                    }
                    checktxtime += std::chrono::seconds(10);
                }
            }
        }
        ENTER_CRITICAL_SECTION(cs_main);

        if (!IsRPCRunning()) {
            throw JSONRPCError(RPC_CLIENT_NOT_CONNECTED, "Shutting down");
        }
        // TODO: Maybe recheck connections/IBD and (if something wrong) send an
        // expires-immediately template to stop miners?
    }

    // Update block
    static CBlockIndex *pindexPrev;
    static int64_t nStart;
    static std::unique_ptr<CBlockTemplate> pblocktemplate;
    if (pindexPrev != ::ChainActive().Tip() ||
        (mempool.GetTransactionsUpdated() != nTransactionsUpdatedLast &&
         GetTime() - nStart > 5)) {
        // Clear pindexPrev so future calls make a new block, despite any
        // failures from here on
        pindexPrev = nullptr;

        // Store the pindexBest used before CreateNewBlock, to avoid races
        nTransactionsUpdatedLast = g_mempool.GetTransactionsUpdated();
        CBlockIndex *pindexPrevNew = chainActive.Tip();
        // nStart = GetTime();

        // Create new block
        CScript scriptDummy = CScript() << OP_TRUE;
        pblocktemplate =
            BlockAssembler(config, mempool).CreateNewBlock(scriptDummy);
        if (!pblocktemplate) {
            throw JSONRPCError(RPC_OUT_OF_MEMORY, "Out of memory");
        }

        // Need to update only after we know CreateNewBlock succeeded
        pindexPrev = pindexPrevNew;
    }

    CHECK_NONFATAL(pindexPrev);
    // pointer for convenience
    CBlock *pblock = &pblocktemplate->block;
    const Consensus::Params &consensusParams =
        config.GetChainParams().GetConsensus();
    //  inject BTC.COM extra transactions
    if (!injectTxs.empty()) {
        for (auto &tx : injectTxs) {
            pblock->vtx.push_back(MakeTransactionRef(std::move(tx)));
        }
        if (IsMagneticAnomalyEnabled(consensusParams, pindexPrev)) {
            // If magnetic anomaly is enabled, we make sure transaction are
            // canonically ordered.
            std::sort(std::begin(pblock->vtx) + 1, std::end(pblock->vtx),
                      [](const std::shared_ptr<const CTransaction> &a,
                         const std::shared_ptr<const CTransaction> &b) -> bool {
                          // The hash is a little endian uint8_t[256] in memory,
                          // so a < b is ordered by ascending.
                          return a->GetId() < b->GetId();
                      });
        }
    }

    // Update nTime
    UpdateTime(pblock, chainparams, pindexPrev);
    pblock->nNonce = 0;

    UniValue aCaps(UniValue::VARR);
    aCaps.push_back("proposal");

    uint160 jobId;                         //  light version
    UniValue merklebranch(UniValue::VARR); //  light version
    UniValue transactions(UniValue::VARR);
    if (lightVersion) {
        std::vector<uint256> vtxhashsNoCoinbase; // txs without coinbase
        for (const auto &it : pblock->vtx) {
            const CTransaction &tx = *it;
            uint256 txId = tx.GetId();

            if (tx.IsCoinBase()) {
                continue;
            }
            vtxhashsNoCoinbase.push_back(txId);
        }
        // merkle branch, merkleBranch_ could be empty
        // make merkleSteps and merkle branch
        std::vector<uint256> merkleSteps;
        makeMerkleBranch(vtxhashsNoCoinbase, merkleSteps);
        for (auto &h : merkleSteps) {
            merklebranch.push_back(h.GetHex());
        }

        std::string jobIdHashSource = pblock->hashPrevBlock.GetHex();
        for (auto &m : merkleSteps) {
            jobIdHashSource += m.GetHex();
        }

        jobId = Hash160(std::vector<uint8_t>(
            {jobIdHashSource.begin(), jobIdHashSource.end()}));

    } else {
        std::map<uint256, int64_t> setTxIndex;
        int i = 0;
        for (const auto &it : pblock->vtx) {
            const CTransaction &tx = *it;
            uint256 txId = tx.GetId();
            setTxIndex[txId] = i++;

            if (tx.IsCoinBase()) {
                continue;
            }

            UniValue entry(UniValue::VOBJ);

            entry.pushKV("data", EncodeHexTx(tx));
            entry.pushKV("txid", txId.GetHex());
            entry.pushKV("hash", tx.GetHash().GetHex());

            UniValue deps(UniValue::VARR);
            for (const CTxIn &in : tx.vin) {
                if (setTxIndex.count(in.prevout.GetTxId())) {
                    deps.push_back(setTxIndex[in.prevout.GetTxId()]);
                }
            }
            entry.pushKV("depends", deps);

            int index_in_template = i - 1;
            entry.pushKV("fee",
                         pblocktemplate->entries[index_in_template].txFee /
                             SATOSHI);
            int64_t nTxSigOps =
                pblocktemplate->entries[index_in_template].txSigOps;
            entry.pushKV("sigops", nTxSigOps);

            transactions.push_back(entry);
        }
    }

    UniValue aux(UniValue::VOBJ);

    UniValue minerFundList(UniValue::VARR);
    const Consensus::Params &consensusParams = chainparams.GetConsensus();
    for (auto fundDestination :
         GetMinerFundWhitelist(consensusParams, pindexPrev)) {
        minerFundList.push_back(EncodeCashAddr(fundDestination, chainparams));
    }

    int64_t minerFundMinValue = 0;
    if (IsAxionEnabled(consensusParams, pindexPrev)) {
        minerFundMinValue =
            int64_t(GetMinerFundAmount(coinbasevalue) / SATOSHI);
    }

    UniValue minerFund(UniValue::VOBJ);
    minerFund.pushKV("addresses", minerFundList);
    minerFund.pushKV("minimumvalue", minerFundMinValue);

    UniValue coinbasetxn(UniValue::VOBJ);
    coinbasetxn.pushKV("minerfund", minerFund);

    arith_uint256 hashTarget = arith_uint256().SetCompact(pblock->nBits);

    UniValue aMutable(UniValue::VARR);
    aMutable.push_back("time");
    if (!lightVersion) {
        //  ganibc: Question, is this related to transactions generated above?
        //  For now, I assume it is, that's why I only push_back when it's not
        //  light version
        aMutable.push_back("transactions");
    }
    aMutable.push_back("prevblock");

    UniValue result(UniValue::VOBJ);
    result.pushKV("capabilities", aCaps);

    result.pushKV("version", pblock->nVersion);

    result.pushKV("previousblockhash", pblock->hashPrevBlock.GetHex());
    if (lightVersion) {
        result.pushKV("job_id", jobId.GetHex());
        result.pushKV("merkle", merklebranch);
    } else {
        result.pushKV("transactions", transactions);
    }
    result.pushKV("coinbaseaux", aux);
    result.pushKV("coinbasetxn", coinbasetxn);
    result.pushKV("coinbasevalue", int64_t(coinbasevalue / SATOSHI));
    result.pushKV("longpollid", ::ChainActive().Tip()->GetBlockHash().GetHex() +
                                    i64tostr(nTransactionsUpdatedLast));
    result.pushKV("target", hashTarget.GetHex());
    result.pushKV("mintime", int64_t(pindexPrev->GetMedianTimePast()) + 1);
    result.pushKV("mutable", aMutable);
    result.pushKV("noncerange", "00000000ffffffff");
    result.pushKV("sigoplimit",
                  GetMaxBlockSigChecksCount(DEFAULT_MAX_BLOCK_SIZE));
    result.pushKV("sizelimit", DEFAULT_MAX_BLOCK_SIZE);
    result.pushKV("curtime", pblock->GetBlockTime());
    result.pushKV("bits", strprintf("%08x", pblock->nBits));
    result.pushKV("height", int64_t(pindexPrev->nHeight) + 1);

    if (lightVersion) {
        std::vector<CTransactionRef> storeTxs;
        auto vtxIterAfterCoinbase = std::next(pblock->vtx.begin());
        storeTxs.insert(storeTxs.begin(), vtxIterAfterCoinbase,
                        pblock->vtx.end());

        const std::string jobIdStr = jobId.GetHex();
        fs::path outputFile = GetblocktemplatelightDataDir();
        outputFile += jobIdStr;
        if (!fs::exists(outputFile)) {
            CDataStream datastream(SER_DISK, PROTOCOL_VERSION);

            datastream << (uint32_t)storeTxs.size();
            for (const auto &it : storeTxs) {
                const CTransaction &tx = *it;
                datastream << tx;
            }

            fs::ofstream ofile(outputFile);
            if (ofile.is_open()) {
                ofile << "GBT";
                ofile.write(datastream.data(), datastream.size());
                ofile << "GBT";
                LogPrintf("getblocktemplatelight written to %s",
                          outputFile.string().c_str());
            } else {
                LogPrintf("getblocktemplatelight cannot write tx data to %s",
                          outputFile.string().c_str());
            }
        }

        {
            LOCK(cs_getblocktemplatelight);
            if ((int)gGetblocktemplatelightCacheMap.size() >=
                GetblocktemplatelightCacheSize()) //  limit the total cache
            {
                //  remove the oldest block
                auto removeJobIdIter = gGetblocktemplatelightIdList.begin();
                if (jobIdStr != *removeJobIdIter) {
                    LogPrintf(
                        "Cache size exceeded. cache for job_id %s removed\n",
                        (*removeJobIdIter).c_str());
                    //  if the oldest block not the same as the latest block,
                    //  then erase.
                    gGetblocktemplatelightCacheMap.erase(*removeJobIdIter);
                }
                gGetblocktemplatelightIdList.erase(removeJobIdIter);
            }
            gGetblocktemplatelightIdList.push_back(jobIdStr);
            gGetblocktemplatelightCacheMap[jobIdStr] = std::move(storeTxs);
        }
    }

    return result;
}

static UniValue getblocktemplatelight(const Config &config,
                                      const JSONRPCRequest &request) {
    return getblocktemplatecommon(true, config, request);
}

static UniValue getblocktemplate(const Config &config,
                                 const JSONRPCRequest &request) {
    return getblocktemplatecommon(false, config, request);
}

class submitblock_StateCatcher : public CValidationInterface {
public:
    uint256 hash;
    bool found;
    BlockValidationState state;

    explicit submitblock_StateCatcher(const uint256 &hashIn)
        : hash(hashIn), found(false), state() {}

protected:
    void BlockChecked(const CBlock &block,
                      const BlockValidationState &stateIn) override {
        if (block.GetHash() != hash) {
            return;
        }

        found = true;
        state = stateIn;
    }
};

static UniValue submitblockcommon(const std::string &jobId,
                                  const Config &config,
                                  const JSONRPCRequest &request) {
    int64_t submitblockStart = GetTimeMicros();
    std::shared_ptr<CBlock> blockptr = std::make_shared<CBlock>();
    CBlock &block = *blockptr;
    if (!DecodeHexBlk(block, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Block decode failed");
    }

    auto timeSerializeTx = GetTimeMicros() - submitblockStart;
    if (!jobId.empty()) {
        if (block.vtx.size() != 1 || !block.vtx[0]->IsCoinBase()) {
            throw JSONRPCError(
                RPC_DESERIALIZATION_ERROR,
                "Block does not only contain a coinbase (light version)");
        }
        bool loadFile = true;
        {
            LOCK(cs_getblocktemplatelight);
            auto iter = gGetblocktemplatelightCacheMap.find(jobId);
            if (iter != gGetblocktemplatelightCacheMap.end()) {
                auto &vtx = iter->second;
                block.vtx.insert(block.vtx.end(), vtx.begin(), vtx.end());
                loadFile = false;
            }
        }

        if (loadFile) {
            LogPrintf("SubmitBlockLight job_id %s not found in mem cache. "
                      "Searching from file.\n",
                      jobId.c_str());
            fs::path filename = GetblocktemplatelightDataDir();
            filename += jobId;
            if (!fs::exists(filename)) {
                LogPrintf("[WARNING] SubmitBlockLight cannot find file %s. "
                          "Searching trash dir.\n",
                          jobId.c_str());
                filename = GetblocktemplatelightDataTrashDir();
                filename += jobId;
            }
            LogPrintf("SubmitBlockLight job_id %s found in %s.\n",
                      jobId.c_str(), filename.string().c_str());
            std::vector<char> dataBuff;
            {
                fs::ifstream file(filename);
                if (!file.is_open()) {
                    return "job_id data not available";
                }
                file.seekg(0, file.end);
                int64_t fileSize = (int64_t)file.tellg();
                auto dataSize =
                    fileSize - 6; // 6 from prefix GBT (3) and postfix GBT (3)
                if (dataSize <= 0) {
                    return "job_id data is empty";
                }
                file.seekg(3, file.beg);
                dataBuff.resize(dataSize);
                file.read(dataBuff.data(), dataSize);
            }
            CDataStream c(dataBuff, SER_DISK, PROTOCOL_VERSION);
            uint32_t txCount = 0;
            c >> txCount;
            for (uint32_t i = 0; i < txCount; ++i) {
                CMutableTransaction mutableTx;
                c >> mutableTx;
                block.vtx.push_back(MakeTransactionRef(std::move(mutableTx)));
            }
        }
        timeSerializeTx = GetTimeMicros() - submitblockStart;

    } else {
        if (block.vtx.empty() || !block.vtx[0]->IsCoinBase()) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                               "Block does not start with a coinbase");
        }
    }

    const BlockHash hash = block.GetHash();
    {
        LOCK(cs_main);
        const CBlockIndex *pindex = LookupBlockIndex(hash);
        if (pindex) {
            if (pindex->IsValid(BlockValidity::SCRIPTS)) {
                return "duplicate";
            }
            if (pindex->nStatus.isInvalid()) {
                return "duplicate-invalid";
            }
        }
    }

    bool new_block;
    submitblock_StateCatcher sc(block.GetHash());
    RegisterValidationInterface(&sc);
    bool accepted =
        ProcessNewBlock(config, blockptr, /* fForceProcessing */ true,
                        /* fNewBlock */ &new_block);
    // We are only interested in BlockChecked which will have been dispatched
    // in-thread, so no need to sync before unregistering.
    UnregisterValidationInterface(&sc);
    // Sync to ensure that the catcher's slots aren't executing when it goes out
    // of scope and is deleted.
    SyncWithValidationInterfaceQueue();
    if (!new_block && accepted) {
        return "duplicate";
    }

    if (!sc.found) {
        return "inconclusive";
    }

    auto result = BIP22ValidationResult(config, sc.state);

    int64_t submitblockEnd = GetTimeMicros();
    auto timeLen = submitblockEnd - submitblockStart;
    if (!jobId.empty()) {
        LogPrintf("SubmitBlockLight serialize txs for job_id %s duration is %f "
                  "seconds\n",
                  jobId.c_str(), (float)timeSerializeTx * 0.000001f);
    }
    LogPrintf("SubmitBlock duration is %f seconds\n",
              (float)timeLen * 0.000001f);

    return result;
}

static UniValue submitblock(const Config &config,
                            const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() < 1 ||
        request.params.size() > 2) {
        throw std::runtime_error(
            "submitblock \"hexdata\" ( \"jsonparametersobject\" )\n"
            "\nAttempts to submit new block to network.\n"
            "The 'jsonparametersobject' parameter is currently ignored.\n"
            "See https://en.bitcoin.it/wiki/BIP_0022 for full specification.\n"

            "\nArguments\n"
            "1. \"hexdata\"        (string, required) the hex-encoded block "
            "data to submit\n"
            "2. \"parameters\"     (string, optional) object of optional "
            "parameters\n"
            "    {\n"
            "      \"workid\" : \"id\"    (string, optional) if the server "
            "provided a workid, it MUST be included with submissions\n"
            "    }\n"
            "\nResult:\n"
            "\nExamples:\n" +
            HelpExampleCli("submitblock", "\"mydata\"") +
            HelpExampleRpc("submitblock", "\"mydata\""));
    }

    return submitblockcommon("", config, request);
}

static UniValue submitblocklight(const Config &config,
                                 const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() < 2 ||
        request.params.size() > 3) {
        throw std::runtime_error(
            "submitblocklight \"hexdata\" ( \"jsonparametersobject\" )\n"
            "\nAttempts to submit new block to network.\n"
            "The 'jsonparametersobject' parameter is currently ignored.\n"
            "See https://en.bitcoin.it/wiki/BIP_0022 for full specification.\n"

            "\nArguments\n"
            "1. \"hexdata\"        (string, required) the hex-encoded block "
            "data to submit\n"
            "2. \"job_id\"        (string, required) job_id from gbt light\n"
            "3. \"parameters\"     (string, optional) object of optional "
            "parameters\n"
            "    {\n"
            "      \"workid\" : \"id\"    (string, optional) if the server "
            "provided a workid, it MUST be included with submissions\n"
            "    }\n"
            "\nResult:\n"
            "\nExamples:\n" +
            HelpExampleCli("submitblocklight", "\"mydata\"") +
            HelpExampleRpc("submitblocklight", "\"mydata\""));
    }

    std::string jobId = request.params[1].get_str();
    return submitblockcommon(jobId, config, request);
}

static UniValue submitheader(const Config &config,
                             const JSONRPCRequest &request) {
    RPCHelpMan{
        "submitheader",
        "Decode the given hexdata as a header and submit it as a candidate "
        "chain tip if valid."
        "\nThrows when the header is invalid.\n",
        {
            {"hexdata", RPCArg::Type::STR_HEX, RPCArg::Optional::NO,
             "the hex-encoded block header data"},
        },
        RPCResult{RPCResult::Type::NONE, "", "None"},
        RPCExamples{HelpExampleCli("submitheader", "\"aabbcc\"") +
                    HelpExampleRpc("submitheader", "\"aabbcc\"")},
    }
        .Check(request);

    CBlockHeader h;
    if (!DecodeHexBlockHeader(h, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                           "Block header decode failed");
    }
    {
        LOCK(cs_main);
        if (!LookupBlockIndex(h.hashPrevBlock)) {
            throw JSONRPCError(RPC_VERIFY_ERROR,
                               "Must submit previous header (" +
                                   h.hashPrevBlock.GetHex() + ") first");
        }
    }

    BlockValidationState state;
    ProcessNewBlockHeaders(config, {h}, state);
    if (state.IsValid()) {
        return NullUniValue;
    }
    if (state.IsError()) {
        throw JSONRPCError(RPC_VERIFY_ERROR, state.ToString());
    }
    throw JSONRPCError(RPC_VERIFY_ERROR, state.GetRejectReason());
}

static UniValue estimatefee(const Config &config,
                            const JSONRPCRequest &request) {
    RPCHelpMan{
        "estimatefee",
        "Estimates the approximate fee per kilobyte needed for a "
        "transaction\n",
        {},
        RPCResult{RPCResult::Type::NUM, "", "estimated fee-per-kilobyte"},
        RPCExamples{HelpExampleCli("estimatefee", "")},
    }
        .Check(request);

    const CTxMemPool &mempool = EnsureMemPool(request.context);
    return ValueFromAmount(mempool.estimateFee().GetFeePerK());
}

// clang-format off
static const CRPCCommand commands[] = {
    //  category   name                     actor (function)       argNames
    //  ---------- ------------------------ ---------------------- ----------
    {"mining",     "getnetworkhashps",      getnetworkhashps,      {"nblocks", "height"}},
    {"mining",     "getmininginfo",         getmininginfo,         {}},
    {"mining",     "prioritisetransaction", prioritisetransaction, {"txid", "dummy", "fee_delta"}},
    {"mining",     "getblocktemplate",      getblocktemplate,      {"template_request"}},
    {"mining",     "getblocktemplatelight", getblocktemplatelight, {"template_request"}},
    {"mining",     "submitblock",           submitblock,           {"hexdata", "parameters"}},
    {"mining",     "submitblocklight",      submitblocklight,      {"hexdata", "job_id", "parameters"}},
    {"mining",     "submitheader",          submitheader,          {"hexdata"}},

    {"generating", "generatetoaddress",     generatetoaddress,     {"nblocks", "address", "maxtries"}},
    {"generating", "generatetodescriptor",  generatetodescriptor,  {"num_blocks","descriptor","maxtries"}},

    {"util",       "estimatefee",           estimatefee,           {"nblocks"}},
};
// clang-format on

void RegisterMiningRPCCommands(CRPCTable &t) {
    for (unsigned int vcidx = 0; vcidx < ARRAYLEN(commands); vcidx++) {
        t.appendCommand(commands[vcidx].name, &commands[vcidx]);
    }
}
