#include <consensus/merkle.h>
#include <claimtrie.h>
#include <hash.h>

#include <boost/algorithm/string.hpp>
#include <boost/foreach.hpp>
#include <boost/locale.hpp>
#include <boost/locale/conversion.hpp>
#include <boost/locale/localization_backend.hpp>
#include <boost/scope_exit.hpp>

void CClaimTrieCacheExpirationFork::removeAndAddToExpirationQueue(expirationQueueRowType& row, int height, bool increment)
{
    for (auto e = row.begin(); e != row.end(); ++e) {
        // remove and insert with new expiration time
        removeFromExpirationQueue(e->name, e->outPoint, height);
        int extend_expiration = Params().GetConsensus().nExtendedClaimExpirationTime - Params().GetConsensus().nOriginalClaimExpirationTime;
        int new_expiration_height = increment ? height + extend_expiration : height - extend_expiration;
        CNameOutPointType entry(e->name, e->outPoint);
        addToExpirationQueue(new_expiration_height, entry);
    }
}

void CClaimTrieCacheExpirationFork::removeAndAddSupportToExpirationQueue(expirationQueueRowType& row, int height, bool increment)
{
    for (auto e = row.begin(); e != row.end(); ++e) {
        // remove and insert with new expiration time
        removeSupportFromExpirationQueue(e->name, e->outPoint, height);
        int extend_expiration = Params().GetConsensus().nExtendedClaimExpirationTime - Params().GetConsensus().nOriginalClaimExpirationTime;
        int new_expiration_height = increment ? height + extend_expiration : height - extend_expiration;
        CNameOutPointType entry(e->name, e->outPoint);
        addSupportToExpirationQueue(new_expiration_height, entry);
    }
}

bool CClaimTrieCacheExpirationFork::forkForExpirationChange(bool increment)
{
    /*
    If increment is True, we have forked to extend the expiration time, thus items in the expiration queue
    will have their expiration extended by "new expiration time - original expiration time"

    If increment is False, we are decremented a block to reverse the fork. Thus items in the expiration queue
    will have their expiration extension removed.
    */

    //look through db for expiration queues, if we haven't already found it in dirty expiration queue
    boost::scoped_ptr<CDBIterator> pcursor(base->db->NewIterator());
    for (pcursor->SeekToFirst(); pcursor->Valid(); pcursor->Next()) {
        std::pair<uint8_t, int> key;
        if (!pcursor->GetKey(key))
            continue;
        int height = key.second;
        if (key.first == EXP_QUEUE_ROW) {
            expirationQueueRowType row;
            if (pcursor->GetValue(row)) {
                removeAndAddToExpirationQueue(row, height, increment);
            } else {
                return error("%s(): error reading expiration queue rows from disk", __func__);
            }
        } else if (key.first == SUPPORT_EXP_QUEUE_ROW) {
            expirationQueueRowType row;
            if (pcursor->GetValue(row)) {
                removeAndAddSupportToExpirationQueue(row, height, increment);
            } else {
                return error("%s(): error reading support expiration queue rows from disk", __func__);
            }
        }
    }

    return true;
}

bool CClaimTrieCacheNormalizationFork::shouldNormalize() const
{
    return nNextHeight > Params().GetConsensus().nNormalizedNameForkHeight;
}

std::string CClaimTrieCacheNormalizationFork::normalizeClaimName(const std::string& name, bool force) const
{
    if (!force && !shouldNormalize())
        return name;

    static std::locale utf8;
    static bool initialized = false;
    if (!initialized) {
        static boost::locale::localization_backend_manager manager =
            boost::locale::localization_backend_manager::global();
        manager.select("icu");

        static boost::locale::generator curLocale(manager);
        utf8 = curLocale("en_US.UTF8");
        initialized = true;
    }

    std::string normalized;
    try {
        // Check if it is a valid utf-8 string. If not, it will throw a
        // boost::locale::conv::conversion_error exception which we catch later
        normalized = boost::locale::conv::to_utf<char>(name, "UTF-8", boost::locale::conv::stop);
        if (normalized.empty())
            return name;

        // these methods supposedly only use the "UTF8" portion of the locale object:
        normalized = boost::locale::normalize(normalized, boost::locale::norm_nfd, utf8);
        normalized = boost::locale::fold_case(normalized, utf8);
    } catch (const boost::locale::conv::conversion_error& e) {
        return name;
    } catch (const std::bad_cast& e) {
        LogPrintf("%s() is invalid or dependencies are missing: %s\n", __func__, e.what());
        throw;
    } catch (const std::exception& e) { // TODO: change to use ... with current_exception() in c++11
        LogPrintf("%s() had an unexpected exception: %s\n", __func__, e.what());
        return name;
    }

    return normalized;
}

bool CClaimTrieCacheNormalizationFork::insertClaimIntoTrie(const std::string& name, const CClaimValue& claim, bool fCheckTakeover)
{
    return CClaimTrieCacheExpirationFork::insertClaimIntoTrie(normalizeClaimName(name, overrideInsertNormalization), claim, fCheckTakeover);
}

bool CClaimTrieCacheNormalizationFork::removeClaimFromTrie(const std::string& name, const COutPoint& outPoint, CClaimValue& claim, bool fCheckTakeover)
{
    return CClaimTrieCacheExpirationFork::removeClaimFromTrie(normalizeClaimName(name, overrideRemoveNormalization), outPoint, claim, fCheckTakeover);
}

bool CClaimTrieCacheNormalizationFork::insertSupportIntoMap(const std::string& name, const CSupportValue& support, bool fCheckTakeover)
{
    return CClaimTrieCacheExpirationFork::insertSupportIntoMap(normalizeClaimName(name, overrideInsertNormalization), support, fCheckTakeover);
}

bool CClaimTrieCacheNormalizationFork::removeSupportFromMap(const std::string& name, const COutPoint& outPoint, CSupportValue& support, bool fCheckTakeover)
{
    return CClaimTrieCacheExpirationFork::removeSupportFromMap(normalizeClaimName(name, overrideRemoveNormalization), outPoint, support, fCheckTakeover);
}

bool CClaimTrieCacheNormalizationFork::normalizeAllNamesInTrieIfNecessary(insertUndoType& insertUndo, claimQueueRowType& removeUndo, insertUndoType& insertSupportUndo, supportQueueRowType& expireSupportUndo, std::vector<std::pair<std::string, int>>& takeoverHeightUndo)
{
    if (nNextHeight != Params().GetConsensus().nNormalizedNameForkHeight)
        return false;

    // run the one-time upgrade of all names that need to change
    // it modifies the (cache) trie as it goes, so we need to grab everything to be modified first

    for (auto it = base->begin(); it != base->end(); ++it) {
        const std::string normalized = normalizeClaimName(it.key(), true);
        if (normalized == it.key())
            continue;

        auto supports = getSupportsForName(it.key());
        for (auto& support : supports) {
            // if it's already going to expire just skip it
            if (support.nHeight + base->nExpirationTime <= nNextHeight)
                continue;

            CSupportValue removed;
            assert(removeSupportFromMap(it.key(), support.outPoint, removed, false));
            expireSupportUndo.emplace_back(it.key(), removed);
            assert(insertSupportIntoMap(normalized, support, false));
            insertSupportUndo.emplace_back(it.key(), support.outPoint, -1);
        }

        namesToCheckForTakeover.insert(normalized);

        auto cached = cacheData(it.key(), false);
        if (!cached || cached->claims.empty())
            continue;

        for (auto& claim : it->claims) {
            if (claim.nHeight + base->nExpirationTime <= nNextHeight)
                continue;

            CClaimValue removed;
            assert(removeClaimFromTrie(it.key(), claim.outPoint, removed, false));
            removeUndo.emplace_back(it.key(), removed);
            assert(insertClaimIntoTrie(normalized, claim, false));
            insertUndo.emplace_back(it.key(), claim.outPoint, -1);
        }

        takeoverHeightUndo.emplace_back(it.key(), it->nHeightOfLastTakeover);
    }
    return true;
}

bool CClaimTrieCacheNormalizationFork::incrementBlock(insertUndoType& insertUndo, claimQueueRowType& expireUndo, insertUndoType& insertSupportUndo, supportQueueRowType& expireSupportUndo, std::vector<std::pair<std::string, int>>& takeoverHeightUndo)
{
    overrideInsertNormalization = normalizeAllNamesInTrieIfNecessary(insertUndo, expireUndo, insertSupportUndo, expireSupportUndo, takeoverHeightUndo);
    BOOST_SCOPE_EXIT(&overrideInsertNormalization) { overrideInsertNormalization = false; }
    BOOST_SCOPE_EXIT_END
    return CClaimTrieCacheExpirationFork::incrementBlock(insertUndo, expireUndo, insertSupportUndo, expireSupportUndo, takeoverHeightUndo);
}

bool CClaimTrieCacheNormalizationFork::decrementBlock(insertUndoType& insertUndo, claimQueueRowType& expireUndo, insertUndoType& insertSupportUndo, supportQueueRowType& expireSupportUndo)
{
    overrideRemoveNormalization = shouldNormalize();
    BOOST_SCOPE_EXIT(&overrideRemoveNormalization) { overrideRemoveNormalization = false; }
    BOOST_SCOPE_EXIT_END
    return CClaimTrieCacheExpirationFork::decrementBlock(insertUndo, expireUndo, insertSupportUndo, expireSupportUndo);
}

bool CClaimTrieCacheNormalizationFork::getProofForName(const std::string& name, CClaimTrieProof& proof)
{
    return CClaimTrieCacheExpirationFork::getProofForName(normalizeClaimName(name), proof);
}

bool CClaimTrieCacheNormalizationFork::getInfoForName(const std::string& name, CClaimValue& claim) const
{
    return CClaimTrieCacheExpirationFork::getInfoForName(normalizeClaimName(name), claim);
}

CClaimsForNameType CClaimTrieCacheNormalizationFork::getClaimsForName(const std::string& name) const
{
    return CClaimTrieCacheExpirationFork::getClaimsForName(normalizeClaimName(name));
}

int CClaimTrieCacheNormalizationFork::getDelayForName(const std::string& name, const uint160& claimId)
{
    return CClaimTrieCacheExpirationFork::getDelayForName(normalizeClaimName(name), claimId);
}

bool CClaimTrieCacheNormalizationFork::addClaimToQueues(const std::string& name, const CClaimValue& claim)
{
    return CClaimTrieCacheExpirationFork::addClaimToQueues(normalizeClaimName(name, claim.nValidAtHeight > Params().GetConsensus().nNormalizedNameForkHeight), claim);
}

bool CClaimTrieCacheNormalizationFork::addSupportToQueues(const std::string& name, const CSupportValue& support)
{
    return CClaimTrieCacheExpirationFork::addSupportToQueues(normalizeClaimName(name, support.nValidAtHeight > Params().GetConsensus().nNormalizedNameForkHeight), support);
}

std::string CClaimTrieCacheNormalizationFork::adjustNameForValidHeight(const std::string& name, int validHeight) const
{
    return normalizeClaimName(name, validHeight > Params().GetConsensus().nNormalizedNameForkHeight);
}

CClaimTrieCacheHashFork::CClaimTrieCacheHashFork(CClaimTrie* base, bool fRequireTakeoverHeights)
    : CClaimTrieCacheNormalizationFork(base, fRequireTakeoverHeights)
{
}

static const uint256 leafHash = uint256S("0000000000000000000000000000000000000000000000000000000000000002");
static const uint256 emptyHash = uint256S("0000000000000000000000000000000000000000000000000000000000000003");

uint256 Hash(int64_t value)
{
    std::array<uint8_t, sizeof(value)> vch;
    for (std::size_t i = 0; i < vch.size(); ++i)
        vch[i] = (value >> ((vch.size() - i - 1) * 8)) & 0xff;
    return Hash(vch.begin(), vch.end());
}

std::vector<uint256> getNodeHash(CClaimTrie::const_iterator it)
{
    std::vector<uint256> hashes;
    for (auto& claim : it->claims) {
        auto& hash = claim.outPoint.hash;
        hashes.push_back(Hash(hash.begin(), hash.end()));
        hashes.push_back(Hash(claim.outPoint.n));
        hashes.push_back(Hash(claim.nEffectiveAmount));
        hashes.push_back(Hash(claim.nValidAtHeight));
    }
    hashes.push_back(Hash(it->nHeightOfLastTakeover));
    return hashes;
}

template <typename T>
using iCbType = std::function<void(T&)>;

template <typename TIterator>
uint256 recursiveMerkleHash(TIterator& it, const iCbType<TIterator>& process, const iCbType<TIterator>& verify = {})
{
    std::vector<uint256> childHashes;
    for (auto& child : it.children()) {
        process(child);
        childHashes.push_back(child->hash);
    }

    std::vector<uint256> claimHashes;
    if (!it->empty()) {
        claimHashes = getNodeHash(it);
    } else if (verify) {
        verify(it);
    }

    auto left = childHashes.empty() ? leafHash : ComputeMerkleRoot(childHashes);
    auto right = claimHashes.empty() ? emptyHash : ComputeMerkleRoot(claimHashes);

    return Hash(left.begin(), left.end(), right.begin(), right.end());
}

uint256 CClaimTrieCacheHashFork::recursiveComputeMerkleHash(CClaimTrie::iterator& it)
{
    if (nNextHeight < Params().GetConsensus().nAllClaimsInMerkleForkHeight)
        return CClaimTrieCacheBase::recursiveComputeMerkleHash(it);

    using iterator = CClaimTrie::iterator;
    iCbType<iterator> process = [&process](iterator& it) {
        if (it->hash.IsNull())
            it->hash = recursiveMerkleHash(it, process);
    };
    process(it);
    return it->hash;
}

bool CClaimTrieCacheHashFork::recursiveCheckConsistency(CClaimTrie::const_iterator& it, int minimumHeight, std::string& failed) const
{
    if (nNextHeight < Params().GetConsensus().nAllClaimsInMerkleForkHeight)
        return CClaimTrieCacheBase::recursiveCheckConsistency(it, minimumHeight, failed);

    struct CRecursiveBreak{};

    using iterator = CClaimTrie::const_iterator;
    iCbType<iterator> verify = [&failed](iterator& it) {
        if (!it.hasChildren()) {
            // we don't allow a situation of no children and no claims; no empty leaf nodes allowed
            failed = it.key();
            throw CRecursiveBreak();
        }
    };

    iCbType<iterator> process = [&failed, &process, &verify](iterator& it) {
        if (it->hash != recursiveMerkleHash(it, process, verify)) {
            failed = it.key();
            throw CRecursiveBreak();
        }
    };

    try {
        process(it);
    } catch (const CRecursiveBreak&) {
        return false;
    }
    return true;
}

std::vector<uint256> ComputeMerklePath(const std::vector<uint256>& hashes, uint32_t idx)
{
    std::vector<uint256> res;
    uint32_t count = 0;
    uint256 inner[32];
    int matchlevel = -1;
    while (count < hashes.size()) {
        uint256 h = hashes[count];
        bool matchh = count == idx;
        count++;
        int level;
        for (level = 0; !(count & (1 << level)); level++) {
            if (matchh) {
                res.push_back(inner[level]);
            } else if (matchlevel == level) {
                res.push_back(h);
                matchh = true;
            }
            CHash256().Write(inner[level].begin(), 32).Write(h.begin(), 32).Finalize(h.begin());
        }
        // Store the resulting hash at inner position level.
        inner[level] = h;
        if (matchh) {
            matchlevel = level;
        }
    }
    int level = 0;
    while (!(count & (1 << level)))
        level++;

    uint256 h = inner[level];
    bool matchh = matchlevel == level;
    while (count != (1 << level)) {
        // If we reach this point, h is an inner value that is not the top.
        // We combine it with itself (Bitcoin's special rule for odd levels in
        // the tree) to produce a higher level one.
        if (matchh)
            res.push_back(h);

        CHash256().Write(h.begin(), 32).Write(h.begin(), 32).Finalize(h.begin());
        // Increment count to the value it would have if two entries at this
        // level had existed.
        count += (1 << level);
        level++;
        // And propagate the result upwards accordingly.
        while (!(count & (1 << level))) {
            if (matchh) {
                res.push_back(inner[level]);
            } else if (matchlevel == level) {
                res.push_back(h);
                matchh = true;
            }
            CHash256().Write(inner[level].begin(), 32).Write(h.begin(), 32).Finalize(h.begin());
            level++;
        }
    }
    return res;
}

bool CClaimTrieCacheHashFork::getProofForName(const std::string& name, CClaimTrieProof& proof)
{
    if (nNextHeight < Params().GetConsensus().nAllClaimsInMerkleForkHeight)
        return CClaimTrieCacheBase::getProofForName(name, proof);

    auto fillPairs = [&proof](const std::vector<uint256>& hashes, uint32_t idx) {
        auto partials = ComputeMerklePath(hashes, idx);
        for (auto it = partials.rbegin(); it != partials.rend(); ++it) {
            proof.pairs.emplace_back(bool(idx & 1), *it);
            idx >>= 1;
        }
    };

    // cache the parent nodes
    cacheData(name, false);
    getMerkleHash();
    proof.hasValue = false;
    proof.nHeightOfLastTakeover = 0;
    for (const auto& it : cache.nodes(name)) {
        std::vector<uint256> childHashes;
        uint32_t nextCurrentIdx = 0;
        for (const auto& child : it.children()) {
            if (name.find(child.key()) == 0)
                nextCurrentIdx = uint32_t(childHashes.size());
            childHashes.push_back(child->hash);
        }

        std::vector<uint256> claimHashes;
        if (!it->empty())
            claimHashes = getNodeHash(it);

        // I am on a node; I need a hash(children, claims)
        // if I am the last node on the list, it will be hash(children, x)
        // else it will be hash(x, claims)
        if (it.key() == name) {
            CClaimValue claim;
            if (it->getBestClaim(claim)) {
                proof.hasValue = true;
                proof.outPoint = claim.outPoint;
            }
            auto hash = childHashes.empty() ? leafHash : ComputeMerkleRoot(childHashes);
            proof.pairs.emplace_back(true, hash);
            if (!claimHashes.empty())
                fillPairs(claimHashes, 0);
        } else {
            auto hash = claimHashes.empty() ? emptyHash : ComputeMerkleRoot(claimHashes);
            proof.pairs.emplace_back(false, hash);
            if (!childHashes.empty())
                fillPairs(childHashes, nextCurrentIdx);
        }
    }
    std::reverse(proof.pairs.begin(), proof.pairs.end());
    return true;
}
