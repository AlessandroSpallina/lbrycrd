// Copyright (c) 2018 The LBRY developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <coins.h>
#include <claimscriptop.h>
#include <nameclaim.h>

CClaimScriptAddOp::CClaimScriptAddOp(const COutPoint& point, CAmount nValue, int nHeight)
    : point(point), nValue(nValue), nHeight(nHeight)
{
}

bool CClaimScriptAddOp::claimName(CClaimTrieCache& trieCache, const std::string& name)
{
    return addClaim(trieCache, name, ClaimIdHash(point.hash, point.n));
}

bool CClaimScriptAddOp::updateClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    return addClaim(trieCache, name, claimId);
}

bool CClaimScriptAddOp::addClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    return trieCache.addClaim(name, point, claimId, nValue, nHeight);
}

bool CClaimScriptAddOp::supportClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    return trieCache.addSupport(name, point, nValue, claimId, nHeight);
}

CClaimScriptUndoAddOp::CClaimScriptUndoAddOp(const COutPoint& point, int nHeight) : point(point), nHeight(nHeight)
{
}

bool CClaimScriptUndoAddOp::claimName(CClaimTrieCache& trieCache, const std::string& name)
{
    auto claimId = ClaimIdHash(point.hash, point.n);
    LogPrintf("--- [%lu]: OP_CLAIM_NAME \"%s\" with claimId %s and tx prevout %s at index %d\n", nHeight, name, claimId.GetHex(), point.hash.ToString(), point.n);
    return undoAddClaim(trieCache, name, claimId);
}

bool CClaimScriptUndoAddOp::updateClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    LogPrintf("--- [%lu]: OP_UPDATE_CLAIM \"%s\" with claimId %s and tx prevout %s at index %d\n", nHeight, name, claimId.GetHex(), point.hash.ToString(), point.n);
    return undoAddClaim(trieCache, name, claimId);
}

bool CClaimScriptUndoAddOp::undoAddClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    LogPrintf("%s: (txid: %s, nOut: %d) Removing %s, claimId: %s, from the claim trie due to block disconnect\n", __func__, point.hash.ToString(), point.n, name, claimId.ToString());
    bool res = trieCache.undoAddClaim(name, point, nHeight);
    if (!res)
        LogPrintf("%s: Removing fails\n", __func__);
    return res;
}

bool CClaimScriptUndoAddOp::supportClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    LogPrintf("--- [%lu]: OP_SUPPORT_CLAIM \"%s\" with claimId %s and tx prevout %s at index %d\n", nHeight, name, claimId.GetHex(), point.hash.ToString(), point.n);
    LogPrintf("%s: (txid: %s, nOut: %d) Removing support for %s, claimId: %s, from the claim trie due to block disconnect\n", __func__, point.hash.ToString(), point.n, name, claimId.ToString());
    bool res = trieCache.undoAddSupport(name, point, nHeight);
    if (!res)
        LogPrintf("%s: Removing support fails\n", __func__);
    return res;
}

CClaimScriptSpendOp::CClaimScriptSpendOp(const COutPoint& point, int nHeight, int& nValidHeight)
    : point(point), nHeight(nHeight), nValidHeight(nValidHeight)
{
}

bool CClaimScriptSpendOp::claimName(CClaimTrieCache& trieCache, const std::string& name)
{
    auto claimId = ClaimIdHash(point.hash, point.n);
    LogPrintf("+++ [%lu]: OP_CLAIM_NAME \"%s\" with claimId %s and tx prevout %s at index %d\n", nHeight, name, claimId.GetHex(), point.hash.ToString(), point.n);
    return spendClaim(trieCache, name, claimId);
}

bool CClaimScriptSpendOp::updateClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    LogPrintf("+++ [%lu]: OP_UPDATE_CLAIM \"%s\" with claimId %s and tx prevout %s at index %d\n", nHeight, name, claimId.GetHex(), point.hash.ToString(), point.n);
    return spendClaim(trieCache, name, claimId);
}

bool CClaimScriptSpendOp::spendClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    LogPrintf("%s: (txid: %s, nOut: %d) Removing %s, claimId: %s, from the claim trie\n", __func__, point.hash.ToString(), point.n, name, claimId.ToString());
    bool res = trieCache.spendClaim(name, point, nHeight, nValidHeight);
    if (!res)
        LogPrintf("%s: Removing fails\n", __func__);
    return res;
}

bool CClaimScriptSpendOp::supportClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    LogPrintf("+++ [%lu]: OP_SUPPORT_CLAIM \"%s\" with claimId %s and tx prevout %s at index %d\n", nHeight, name, claimId.GetHex(), point.hash.ToString(), point.n);
    LogPrintf("%s: (txid: %s, nOut: %d) Restoring support for %s, claimId: %s, to the claim trie\n", __func__, point.hash.ToString(), point.n, name, claimId.ToString());
    bool res = trieCache.spendSupport(name, point, nHeight, nValidHeight);
    if (!res)
        LogPrintf("%s: Removing support fails\n", __func__);
    return res;
}

CClaimScriptUndoSpendOp::CClaimScriptUndoSpendOp(const COutPoint& point, CAmount nValue, int nHeight, int nValidHeight)
    : point(point), nValue(nValue), nHeight(nHeight), nValidHeight(nValidHeight)
{
}

bool CClaimScriptUndoSpendOp::claimName(CClaimTrieCache& trieCache, const std::string& name)
{
    return undoSpendClaim(trieCache, name, ClaimIdHash(point.hash, point.n));
}

bool CClaimScriptUndoSpendOp::updateClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    return undoSpendClaim(trieCache, name, claimId);
}

bool CClaimScriptUndoSpendOp::undoSpendClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    LogPrintf("%s: (txid: %s, nOut: %d) Restoring %s, claimId: %s, to the claim trie due to block disconnect\n", __func__, point.hash.ToString(), point.n, name, claimId.ToString());
    return trieCache.undoSpendClaim(name, point, claimId, nValue, nHeight, nValidHeight);
}

bool CClaimScriptUndoSpendOp::supportClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId)
{
    LogPrintf("%s: (txid: %s, nOut: %d) Restoring support for %s, claimId: %s, to the claim trie due to block disconnect\n", __func__, point.hash.ToString(), point.n, name, claimId.ToString());
    return trieCache.undoSpendSupport(name, point, claimId, nValue, nHeight, nValidHeight);
}

static std::string vchToString(const std::vector<unsigned char>& name)
{
    return std::string(name.begin(), name.end());
}

bool ProcessClaim(CClaimScriptOp& claimOp, CClaimTrieCache& trieCache, const CScript& scriptPubKey)
{
    int op;
    std::vector<std::vector<unsigned char> > vvchParams;
    if (!DecodeClaimScript(scriptPubKey, op, vvchParams))
        return false;

    switch (op) {
        case OP_CLAIM_NAME:
            return claimOp.claimName(trieCache, vchToString(vvchParams[0]));
        case OP_SUPPORT_CLAIM:
            return claimOp.supportClaim(trieCache, vchToString(vvchParams[0]), uint160(vvchParams[1]));
        case OP_UPDATE_CLAIM:
            return claimOp.updateClaim(trieCache, vchToString(vvchParams[0]), uint160(vvchParams[1]));
    }
    throw std::runtime_error("Unimplemented OP handler.");
}

void UpdateCache(const CTransaction& tx, CClaimTrieCache& trieCache, const CCoinsViewCache& view, int nHeight, const CUpdateCacheCallbacks& callbacks)
{
    class CSpendClaimHistory : public CClaimScriptSpendOp
    {
    public:
        using CClaimScriptSpendOp::CClaimScriptSpendOp;

        bool spendClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId) override
        {
            if (CClaimScriptSpendOp::spendClaim(trieCache, name, claimId)) {
                callback(name, claimId);
                return true;
            }
            return false;
        }
        std::function<void(const std::string& name, const uint160& claimId)> callback;
    };

    spentClaimsType spentClaims;

    for (std::size_t j = 0; j < tx.vin.size(); j++) {
        const CTxIn& txin = tx.vin[j];
        const Coin& coin = view.AccessCoin(txin.prevout);

        CScript scriptPubKey;
        int scriptHeight = nHeight;
        if (coin.out.IsNull() && callbacks.findScriptKey) {
            scriptPubKey = callbacks.findScriptKey(txin.prevout);
        } else {
            scriptHeight = coin.nHeight;
            scriptPubKey = coin.out.scriptPubKey;
        }

        if (scriptPubKey.empty())
            continue;

        int nValidAtHeight;
        CSpendClaimHistory spendClaim(COutPoint(txin.prevout.hash, txin.prevout.n), scriptHeight, nValidAtHeight);
        spendClaim.callback = [&spentClaims](const std::string& name, const uint160& claimId) {
            spentClaims.emplace_back(name, claimId);
        };
        if (ProcessClaim(spendClaim, trieCache, scriptPubKey) && callbacks.claimUndoHeights)
            callbacks.claimUndoHeights(j, nValidAtHeight);
    }

    class CAddSpendClaim : public CClaimScriptAddOp
    {
    public:
        using CClaimScriptAddOp::CClaimScriptAddOp;

        bool updateClaim(CClaimTrieCache& trieCache, const std::string& name, const uint160& claimId) override
        {
            if (callback(name, claimId))
                return CClaimScriptAddOp::updateClaim(trieCache, name, claimId);
            return false;
        }
        std::function<bool(const std::string& name, const uint160& claimId)> callback;
    };

    for (std::size_t j = 0; j < tx.vout.size(); j++) {
        const CTxOut& txout = tx.vout[j];

        if (txout.scriptPubKey.empty())
            continue;

        CAddSpendClaim addClaim(COutPoint(tx.GetHash(), j), txout.nValue, nHeight);
        addClaim.callback = [&trieCache, &spentClaims](const std::string& name, const uint160& claimId) -> bool {
            for (auto itSpent = spentClaims.begin(); itSpent != spentClaims.end(); ++itSpent) {
                if (itSpent->second == claimId && trieCache.normalizeClaimName(name) == trieCache.normalizeClaimName(itSpent->first)) {
                    spentClaims.erase(itSpent);
                    return true;
                }
            }
            return false;
        };
        ProcessClaim(addClaim, trieCache, txout.scriptPubKey);
    }
}
