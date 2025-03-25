#include <iostream>
#include <vector>
#include <unordered_map>
#include <map>
#include <tuple>
#include <string>
#include <algorithm>
#include <cstring>
#include <openssl/hmac.h>
#include <openssl/sha.h>
#include <deque>
#include <set>
#include <functional>
#include <queue>
#include <cassert>
#include <chrono>
// 定义常量
const std::vector<uint8_t> LEFT_BOUND(32, 0x00);   // LEFT_BOUND 等于32个字节的0构成的bytes
const std::vector<uint8_t> RIGHT_BOUND(32, 0xFF);  // RIGHT_BOUND 等于32个字节的0xFF构成的bytes

// 为了能够使用std::vector<uint8_t>作为unordered_map的键，需要一个哈希函数
struct VectorHash {
    size_t operator()(const std::vector<uint8_t>& v) const {
        std::hash<uint8_t> hasher;
        size_t seed = 0;
        for (auto& i : v) {
            seed ^= hasher(i) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};

// 为了能够在std::set中比较std::vector<uint8_t>
struct VectorCompare {
    bool operator()(const std::vector<uint8_t>& a, const std::vector<uint8_t>& b) const {
        return a < b;
    }
};
// 辅助函数：计算SHA256哈希
std::vector<uint8_t> sha256(const std::vector<uint8_t>& data) {
    unsigned char hash[SHA256_DIGEST_LENGTH];
    SHA256_CTX sha256;
    SHA256_Init(&sha256);
    SHA256_Update(&sha256, data.data(), data.size());
    SHA256_Final(hash, &sha256);
    return std::vector<uint8_t>(hash, hash + SHA256_DIGEST_LENGTH);
}

// 辅助函数：使用HMAC-SHA256计算签名
std::vector<uint8_t> hmac_sha256(const std::vector<uint8_t>& key, const std::vector<uint8_t>& data) {
    unsigned char result[SHA256_DIGEST_LENGTH];
    unsigned int result_len = SHA256_DIGEST_LENGTH;
    HMAC(EVP_sha256(), key.data(), key.size(), data.data(), data.size(), result, &result_len);
    return std::vector<uint8_t>(result, result + result_len);
}

// 辅助函数：连接两个vector
std::vector<uint8_t> concat(const std::vector<uint8_t>& a, const std::vector<uint8_t>& b) {
    std::vector<uint8_t> result;
    result.reserve(a.size() + b.size());
    result.insert(result.end(), a.begin(), a.end());
    result.insert(result.end(), b.begin(), b.end());
    return result;
}

// 辅助函数：将整数转换为bytes
std::vector<uint8_t> int_to_bytes(int64_t value, size_t length = 8) {
    std::vector<uint8_t> result(length);
    for (int i = length - 1; i >= 0; i--) {
        result[i] = value & 0xFF;
        value >>= 8;
    }
    return result;
}
/**
 * 基于MCT的子集存在性验证对象VO。
 * VO由VO_Chain和VO_Tree两部分组成，并且在递归调用的过程中全程维护。
 * - VO_Chain: [(HASH, HASH_next, ChainNodeSig, idx)]
 * - VO_Tree: (Nodes: NodeID:Long-> HASH, RootNodeSignature:HASH, NumLeaf:Long)
 */
class MCTSubsetVerificationObject {
public:
    // 构造函数

     MCTSubsetVerificationObject() : tree_num_leaf(0), tree_root_signature() {}

    MCTSubsetVerificationObject(int num_element_in_set) : tree_num_leaf(num_element_in_set), tree_root_signature() {}

    // 添加一个链式证明节点
    void add_chain_node(const std::vector<uint8_t>& element, 
                        const std::vector<uint8_t>& next_element, 
                        const std::vector<uint8_t>& chain_node_signature,
                        int idx) {
        chain.push_back(std::make_tuple(element, next_element, chain_node_signature, idx));
    }

    // 添加一个树状证明节点
    void add_tree_node(int node_id, const std::vector<uint8_t>& hash) {
        tree[node_id] = hash;
    }

    // 设置树根签名
    void set_tree_root_signature(const std::vector<uint8_t>& signature) {
        tree_root_signature = signature;
    }

    // 验证VO
    std::tuple<bool, std::vector<std::vector<uint8_t>>, std::vector<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>>> 
    verify(const std::vector<uint8_t>& sk, const std::vector<std::vector<uint8_t>>& query_subset) const{
        std::vector<std::vector<uint8_t>> subset;
        std::vector<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>> set_ranges;

        // 验证逻辑
        if (tree_root_signature.empty()) {
            // 不包含VO_Tree的情况，采用全链模式
            if (chain.empty()) {
                return std::make_tuple(false, std::vector<std::vector<uint8_t>>(), std::vector<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>>());
            }

            std::set<std::vector<uint8_t>> unique_elements;
            
            for (const auto& t : chain) {
                const std::vector<uint8_t>& element = std::get<0>(t);
                const std::vector<uint8_t>& next_element = std::get<1>(t);
                const std::vector<uint8_t>& chain_node_signature = std::get<2>(t);
                int idx = std::get<3>(t);

                // 计算签名
                std::vector<uint8_t> key = concat(element, concat(
                    std::vector<uint8_t>{0x7C}, // '|' 字符的 ASCII 码
                    concat(next_element, concat(
                        std::vector<uint8_t>{0x7C}, // '|' 字符的 ASCII 码
                        int_to_bytes(idx)
                    ))
                ));
                
                std::vector<uint8_t> signature = hmac_sha256(sk, key);
                
                if (signature != chain_node_signature) {
                    std::cout << "链节点验证失败" << std::endl;
                    return std::make_tuple(false, std::vector<std::vector<uint8_t>>(), std::vector<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>>());
                }
                
                set_ranges.push_back(std::make_tuple(element, next_element));
                unique_elements.insert(element);
                unique_elements.insert(next_element);
            }

            subset.assign(unique_elements.begin(), unique_elements.end());
            
            // 验证查询子集中的所有元素是否存在
            for (const auto& e : query_subset) {
                bool found = false;
                for (const auto& s : subset) {
                    if (s == e) {
                        found = true;
                        break;
                    }
                }
                
                if (!found) {
                    std::cout << "子集验证失败，元素不存在" << std::endl;
                    return std::make_tuple(false, subset, set_ranges);
                }
            }
            
            return std::make_tuple(true, subset, set_ranges);
        } else {
            // 包含VO_Tree的情况，采用树状模式
            // 构建Merkle哈希树结构
            auto tree_structure = build_tree_structure(tree_num_leaf);
            std::vector<int>& left_child_ids = std::get<0>(tree_structure);
            std::vector<int>& right_child_ids = std::get<1>(tree_structure);
            std::unordered_map<int, int>& father_ids = std::get<2>(tree_structure);
            
            // 先验证VO_Chain中所有Tuple
            for (const auto& t : chain) {
                const std::vector<uint8_t>& element = std::get<0>(t);
                const std::vector<uint8_t>& next_element = std::get<1>(t);
                const std::vector<uint8_t>& chain_node_signature = std::get<2>(t);
                int idx = std::get<3>(t);
                
                std::vector<uint8_t> key = concat(element, concat(
                    std::vector<uint8_t>{0x7C}, // '|' 字符的 ASCII 码
                    concat(next_element, concat(
                        std::vector<uint8_t>{0x7C}, // '|' 字符的 ASCII 码
                        int_to_bytes(idx)
                    ))
                ));
                
                std::vector<uint8_t> signature = hmac_sha256(sk, key);
                
                if (signature != chain_node_signature) {
                    std::cout << "链节点验证失败" << std::endl;
                    return std::make_tuple(false, std::vector<std::vector<uint8_t>>(), std::vector<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>>());
                }
            }
                        // 使用 lambda 递归计算根节点哈希值
            std::function<std::vector<uint8_t>(int)> reconstruct_tree_root_hash = 
                [&](int tree_node_id) -> std::vector<uint8_t> {
                    int lc = left_child_ids[tree_node_id];
                    int rc = right_child_ids[tree_node_id];
                    
                    if (tree_node_id >= tree_num_leaf) {
                        // 非叶节点
                        // 如果VO_Tree.Nodes中包含T的哈希值，返回T的哈希值
                        if (tree.find(tree_node_id) != tree.end()) {
                            return tree.at(tree_node_id);
                        }
                        
                        if (rc == -1) {
                            // 如果没有右孩子
                            return reconstruct_tree_root_hash(lc);
                        }
                        
                        // 如果VO_Tree.Nodes中包含右孩子哈希值，递归计算左孩子哈希值，计算本结点哈希值
                        if (tree.find(rc) != tree.end()) {
                            std::vector<uint8_t> lc_hash = reconstruct_tree_root_hash(lc);
                            if (lc_hash.empty()) {
                                return std::vector<uint8_t>();
                            }
                            std::vector<uint8_t> rc_hash = tree.at(rc);
                            std::vector<uint8_t> my_hash = sha256(
                                concat(lc_hash, concat(std::vector<uint8_t>{0x7C}, rc_hash)) // '|' 字符的 ASCII 码
                            );
                            return my_hash;
                        }
                        
                        // 如果VO_Tree.Nodes中包含左孩子哈希值，递归计算右孩子哈希值，计算本结点哈希值
                        if (tree.find(lc) != tree.end()) {
                            std::vector<uint8_t> lc_hash = tree.at(lc);
                            std::vector<uint8_t> rc_hash = reconstruct_tree_root_hash(rc);
                            if (rc_hash.empty()) {
                                return std::vector<uint8_t>();
                            }
                            std::vector<uint8_t> my_hash = sha256(
                                concat(lc_hash, concat(std::vector<uint8_t>{0x7C}, rc_hash)) // '|' 字符的 ASCII 码
                            );
                            return my_hash;
                        }
                        
                        // 如果VO_Tree.Nodes中不包含左孩子哈希值与右孩子哈希值，递归计算左孩子哈希值与右孩子哈希值，计算本结点哈希值
                        if (tree.find(lc) == tree.end() && tree.find(rc) == tree.end()) {
                            std::vector<uint8_t> lc_hash = reconstruct_tree_root_hash(lc);
                            if (lc_hash.empty()) {
                                return std::vector<uint8_t>();
                            }
                            std::vector<uint8_t> rc_hash = reconstruct_tree_root_hash(rc);
                            if (rc_hash.empty()) {
                                return std::vector<uint8_t>();
                            }
                            std::vector<uint8_t> my_hash = sha256(
                                concat(lc_hash, concat(std::vector<uint8_t>{0x7C}, rc_hash)) // '|' 字符的 ASCII 码
                            );
                            return my_hash;
                        }
                        
                        std::cout << "出现了意外的情况，无法计算中间节点" << tree_node_id << "的哈希值" << std::endl;
                        return std::vector<uint8_t>();
                    } else {
                        // 叶节点
                        if (tree.find(tree_node_id) != tree.end()) {
                            return tree.at(tree_node_id);
                        } else {
                            std::cout << "出现了意外的情况，无法获得叶节点" << tree_node_id << "的哈希值" << std::endl;
                            return std::vector<uint8_t>();
                        }
                    }
                };
            
            std::vector<uint8_t> root_node_hash = reconstruct_tree_root_hash(left_child_ids.size() - 1);
            
            // 输出根节点哈希以便调试
            std::cout << "Root node hash: ";
            for (const auto& byte : root_node_hash) {
                printf("%02x", byte);
            }
            std::cout << std::endl;
            
            std::vector<uint8_t> root_signature = hmac_sha256(sk, root_node_hash);
            
            if (root_signature != tree_root_signature) {
                std::cout << "根节点签名验证失败" << std::endl;
                return std::make_tuple(false, std::vector<std::vector<uint8_t>>(), std::vector<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>>());
            }
            
            // 验证通过，对集合区间进行回放
            std::set<std::vector<uint8_t>> unique_elements;
            std::set<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>> unique_ranges;
            
            for (const auto& t : chain) {
                                const std::vector<uint8_t>& element = std::get<0>(t);
                const std::vector<uint8_t>& next_element = std::get<1>(t);
                unique_elements.insert(element);
                unique_elements.insert(next_element);
                unique_ranges.insert(std::make_tuple(element, next_element));
            }
            
            for (const auto& pair : tree) {
                int tree_node_id = pair.first;
                const std::vector<uint8_t>& node_hash = pair.second;
                
                if (tree_node_id >= tree_num_leaf) {
                    continue; // 跳过非叶节点
                }
                
                unique_elements.insert(node_hash);
                
                if (tree_node_id < tree_num_leaf - 1) {
                    auto next_node_it = tree.find(tree_node_id + 1);
                    if (next_node_it != tree.end()) {
                        unique_ranges.insert(std::make_tuple(node_hash, next_node_it->second));
                    }
                }
            }
            
            subset.assign(unique_elements.begin(), unique_elements.end());
            set_ranges.assign(unique_ranges.begin(), unique_ranges.end());
            
            // 验证查询子集中的所有元素是否存在
            for (const auto& e : query_subset) {
                bool found = false;
                for (const auto& s : subset) {
                    if (s == e) {
                        found = true;
                        break;
                    }
                }
                
                if (!found) {
                    std::cout << "子集验证失败，元素不存在" << std::endl;
                    return std::make_tuple(false, subset, set_ranges);
                }
            }
            
            return std::make_tuple(true, subset, set_ranges);
        }
    }

    // 计算VO大小
    int vo_size() const {
        int size = 8; // level
        
        // chain
        size += 8;
        for (const auto& t : chain) {
            const auto& element = std::get<0>(t);
            const auto& next_element = std::get<1>(t);
            const auto& chain_node_signature = std::get<2>(t);
            size += element.size() + next_element.size() + chain_node_signature.size() + 8;
        }
        
        // tree
        size += 8;
        for (const auto& pair : tree) {
            size += pair.second.size();
        }
        
        // tree_root_signature
        size += 32;
        
        // tree_num_leaf
        size += 8;
        
        return size;
    }

private:
    // 构建Merkle哈希树结构
    std::tuple<std::vector<int>, std::vector<int>, std::unordered_map<int, int>> build_tree_structure(int num_leaf) const {
        std::vector<int> left_child_ids;  // 记录每个节点左孩子的ID
        std::vector<int> right_child_ids; // 记录每个节点右孩子的ID
        std::unordered_map<int, int> father_ids; // 记录每个节点的父节点ID
        std::vector<int> tree_nodes;
        
        for (int i = 0; i < num_leaf; i++) {
            tree_nodes.push_back(1);
            left_child_ids.push_back(-1);
            right_child_ids.push_back(-1);
        }
        
        std::vector<int> nodes_to_process = tree_nodes;
        std::vector<int> new_nodes;
        int current_node_id = 0;
        
        while (nodes_to_process.size() > 1) {
            for (size_t i = 0; i < nodes_to_process.size(); i += 2) {
                if (i + 1 < nodes_to_process.size()) {
                    new_nodes.push_back(1);
                    left_child_ids.push_back(current_node_id);
                    right_child_ids.push_back(current_node_id + 1);
                    father_ids[current_node_id] = tree_nodes.size() + new_nodes.size() - 1;
                    father_ids[current_node_id + 1] = tree_nodes.size() + new_nodes.size() - 1;
                    current_node_id += 2;
                } else {
                    new_nodes.push_back(nodes_to_process[i]);
                    left_child_ids.push_back(current_node_id);
                    right_child_ids.push_back(-1);
                    father_ids[current_node_id] = tree_nodes.size() + new_nodes.size() - 1;
                    current_node_id += 1;
                }
            }
            tree_nodes.insert(tree_nodes.end(), new_nodes.begin(), new_nodes.end());
            nodes_to_process = new_nodes;
            new_nodes.clear();
        }
        
        // 根节点没有父节点
        father_ids[tree_nodes.size() - 1] = -1;
        
        return std::make_tuple(left_child_ids, right_child_ids, father_ids);
    }

public:
    std::vector<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>, std::vector<uint8_t>, int>> chain;
    std::unordered_map<int, std::vector<uint8_t>> tree;
    std::vector<uint8_t> tree_root_signature;
    int tree_num_leaf;
};

/**
 * MerkleChainTree类用于实现Partitioned Merkle Chain Tree结构
 */
class MerkleChainTree {
public:
    // 构造函数

    MerkleChainTree() : prefix_len(0) {}

    MerkleChainTree(const std::vector<std::vector<uint8_t>>& hash_elements, 
                  const std::vector<uint8_t>& sk, 
                  int prefix_len) {
        // 要求传入的hash_elements列表是带有边界值的列表
        assert(hash_elements.front() == LEFT_BOUND);
        assert(hash_elements.back() == RIGHT_BOUND);
        
        // 初始化成员变量
        this->prefix_len = prefix_len;
        
        // 处理hash_elements
        for (const auto& e : hash_elements) {
            this->hash_elements.push_back(std::vector<uint8_t>(e.begin(), e.begin() + prefix_len));
        }
        
        // 排序元素
        std::sort(this->hash_elements.begin(), this->hash_elements.end());
        
        // 构建链节点和树节点
        build_chain_nodes(sk);
        auto result = build_tree_nodes(sk);
        tree_nodes = std::move(std::get<0>(result));
        left_child_ids = std::move(std::get<1>(result));
        right_child_ids = std::move(std::get<2>(result));
        father_ids = std::move(std::get<3>(result));
        
        // 计算树签名
        tree_signature = hmac_sha256(sk, tree_nodes.back());
    }
    
    // 计算VO大小
    int vo_size() const {
        int size = 0;
        size += 8;
        for (const auto& h : hash_elements) {
            size += h.size();
        }
        size += 32 * chain_nodes.size();
        for (const auto& t : tree_nodes) {
            size += t.size();
        }
        size += tree_signature.size();
        size += 8; // prefix_len
        return size;
    }
    
    // 构建链节点验证签名
    void build_chain_nodes(const std::vector<uint8_t>& sk) {
        for (size_t i = 0; i < hash_elements.size() - 1; i++) {
            // 计算e的签名
            std::vector<uint8_t> key = concat(hash_elements[i], concat(
                std::vector<uint8_t>{0x7C}, // '|' 字符的 ASCII 码
                concat(hash_elements[i+1], concat(
                    std::vector<uint8_t>{0x7C}, // '|' 字符的 ASCII 码
                    int_to_bytes(i)
                ))
            ));
            std::vector<uint8_t> signature = hmac_sha256(sk, key);
            chain_nodes.push_back(signature);
        }
    }
    
    // 构建树节点哈希
    std::tuple<std::vector<std::vector<uint8_t>>, std::vector<int>, std::vector<int>, std::unordered_map<int, int>> 
    build_tree_nodes(const std::vector<uint8_t>& sk) {
        std::vector<std::vector<uint8_t>> tree_nodes;
        std::vector<int> left_child_ids; // 记录每个节点左孩子的ID
        std::vector<int> right_child_ids; // 记录每个节点右孩子的ID
        std::unordered_map<int, int> father_ids; // 记录每个节点的父节点ID
        
        // 添加叶节点
        for (const auto& element : hash_elements) {
            tree_nodes.push_back(element);
            left_child_ids.push_back(-1);
            right_child_ids.push_back(-1);
        }
        
        // 构建树结构
        std::vector<std::vector<uint8_t>> nodes_to_process = tree_nodes;
        std::vector<std::vector<uint8_t>> new_nodes;
        int current_node_id = 0;
        
        while (nodes_to_process.size() > 1) {
            for (size_t i = 0; i < nodes_to_process.size(); i += 2) {
                if (i + 1 < nodes_to_process.size()) {
                    // 两个节点合并
                    std::vector<uint8_t> key = concat(nodes_to_process[i], concat(
                        std::vector<uint8_t>{0x7C}, // '|' 字符的 ASCII 码
                        nodes_to_process[i+1]
                    ));
                    std::vector<uint8_t> new_node = sha256(key);
                    new_nodes.push_back(new_node);
                    
                    left_child_ids.push_back(current_node_id);
                    right_child_ids.push_back(current_node_id + 1);
                    father_ids[current_node_id] = tree_nodes.size() + new_nodes.size() - 1;
                    father_ids[current_node_id + 1] = tree_nodes.size() + new_nodes.size() - 1;
                    current_node_id += 2;
                } else {
                    // 只有一个节点，直接上升
                    new_nodes.push_back(nodes_to_process[i]);
                    
                    left_child_ids.push_back(current_node_id);
                    right_child_ids.push_back(-1);
                    father_ids[current_node_id] = tree_nodes.size() + new_nodes.size() - 1;
                    current_node_id += 1;
                }
            }
            
            tree_nodes.insert(tree_nodes.end(), new_nodes.begin(), new_nodes.end());
            nodes_to_process = new_nodes;
            new_nodes.clear();
        }
        
        assert(current_node_id == tree_nodes.size() - 1);
        // 根节点没有父节点
        father_ids[tree_nodes.size() - 1] = -1;
        
        return std::make_tuple(tree_nodes, left_child_ids, right_child_ids, father_ids);
    }

        // 生成子集验证对象
    MCTSubsetVerificationObject generate_subset_verification_object(const std::vector<int>& subset_idx)  const {
        // 验证子集下标的合法性
        for (int idx : subset_idx) {
            assert(idx >= 0 && idx < static_cast<int>(hash_elements.size()));
        }
        
        // 计算构造VO的最小开销
        auto cost_result = calculate_min_cost(subset_idx);
        auto& cost_tree = std::get<0>(cost_result);
        auto& cost_chain = std::get<1>(cost_result);
        
        // 构造验证对象
        return construct_vo(cost_tree, cost_chain, subset_idx);
    }

    // 获取哈希元素列表
const std::vector<std::vector<uint8_t>>& get_hash_elements() const {
    return hash_elements;
}
    
private:
    // 计算构造VO的最小开销
    std::tuple<std::unordered_map<int, std::tuple<int, int>>, std::unordered_map<int, int>> 
    calculate_min_cost(const std::vector<int>& subset_idx) const {
        std::unordered_map<int, std::tuple<int, int>> cost_tree; // 节点ID -> (cost, type)
        std::unordered_map<int, int> cost_chain; // 节点ID -> cost
        
        // 将子集中的每个元素转换为对应的树节点ID
        std::deque<int> node_ids_to_process;
        for (int e : subset_idx) {
            node_ids_to_process.push_back(e);
        }
        
        // 从叶子节点开始向上迭代，直至根节点为止
        std::set<int> processed_nodes;
        int count = 0;
        
        while (!node_ids_to_process.empty()) {
            int node_id = node_ids_to_process.front();
            node_ids_to_process.pop_front();
            
            if (processed_nodes.find(node_id) != processed_nodes.end()) {
                continue;
            }
            
            processed_nodes.insert(node_id);
            count++;
            
            int lc = left_child_ids[node_id];
            int rc = right_child_ids[node_id];
            
            if (node_id < static_cast<int>(hash_elements.size())) {
                // 叶节点
                // 树证明（类型1）：将当前节点的HASH值加入VO。Cost_Tree(T) = Sizeof(HASH) + Sizeof(LONG)
                cost_tree[node_id] = std::make_tuple(tree_nodes[node_id].size() + 8, -1);
                
                // 链证明（类型2）：将当前节点和下一结点的HASH值，以及ChainNode的签名加入VO_Chain
                // Cost_Chain(T) = Sizeof(HASH) * 2 + Sizeof(Signature) + Sizeof(LONG)
                int full_cost = tree_nodes[node_id].size() * 2 + 32 + 8;
                cost_chain[node_id] = 0;
                
                //
                                // 判断相邻节点是否在子集中
                auto it = std::find(subset_idx.begin(), subset_idx.end(), node_id + 1);
                if (it != subset_idx.end()) {
                    cost_chain[node_id] += full_cost / 2;
                }
                
                it = std::find(subset_idx.begin(), subset_idx.end(), node_id - 1);
                if (it != subset_idx.end()) {
                    cost_chain[node_id] += full_cost / 2;
                }
                
                if (cost_chain[node_id] == 0) {
                    cost_chain[node_id] = full_cost;
                }
            } else {
                // 非叶节点
                // 链证明（类型1）：将T_left的链式VO与T_right的链式VO整合，Cost_Chain(T) = Cost_Chain(T_left) + Cost_Chain(T_right)
                int c = 0;
                if (cost_chain.find(lc) != cost_chain.end()) {
                    c += cost_chain[lc];
                }
                if (rc != -1 && cost_chain.find(rc) != cost_chain.end()) {
                    c += cost_chain[rc];
                }
                cost_chain[node_id] = c;
                
                // 树证明：生成MerkleTree证明的方式有4种可能
                if (rc == -1) {
                    // 只有左孩子
                    // 方式1（类型2）:两个叶子结点都采用Merkle Tree证明
                    int c1 = std::get<0>(cost_tree[lc]);
                    // 方式2（类型3）: 左孩子采用Merkle Tree证明，右孩子采用链式证明
                    int c2 = c1;
                    // 方式3（类型4）：左孩子采用链式证明，右孩子采用Merkle Tree证明
                    int c3 = cost_chain[lc] + tree_nodes[node_id].size() + 8;
                    // 方式4（类型5）：两个孩子都采用链式证明
                    int c4 = c3;
                    
                    // 选择最小开销的方式
                    if (c1 <= c2 && c1 <= c3 && c1 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c1, 2);
                    } else if (c2 <= c1 && c2 <= c3 && c2 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c2, 3);
                    } else if (c3 <= c1 && c3 <= c2 && c3 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c3, 4);
                    } else {
                        cost_tree[node_id] = std::make_tuple(c4, 5);
                    }
                } else if (cost_chain.find(lc) != cost_chain.end() && cost_chain.find(rc) != cost_chain.end()) {
                    // 两个孩子都已计算过对应的证明开销
                    // 方式1（类型2）:两个叶子结点都采用Merkle Tree证明
                    int c1 = std::get<0>(cost_tree[lc]) + std::get<0>(cost_tree[rc]);
                    // 方式2（类型3）: 左孩子采用Merkle Tree证明，右孩子采用链式证明
                    int c2 = std::get<0>(cost_tree[lc]) + tree_nodes[rc].size() + 8 + cost_chain[rc];
                    // 方式3（类型4）：左孩子采用链式证明，右孩子采用Merkle Tree证明
                    int c3 = std::get<0>(cost_tree[rc]) + tree_nodes[lc].size() + 8 + cost_chain[lc];
                    // 方式4（类型5）：两个孩子都采用链式证明
                    int c4 = cost_chain[lc] + cost_chain[rc] + tree_nodes[node_id].size() + 8;
                    
                    // 选择最小开销的方式
                    if (c1 <= c2 && c1 <= c3 && c1 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c1, 2);
                    } else if (c2 <= c1 && c2 <= c3 && c2 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c2, 3);
                    } else if (c3 <= c1 && c3 <= c2 && c3 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c3, 4);
                    } else {
                        cost_tree[node_id] = std::make_tuple(c4, 5);
                    }
                } else if (cost_chain.find(lc) != cost_chain.end() && cost_chain.find(rc) == cost_chain.end()) {
                    // 左孩子已经有对应证明开销，右孩子还没有
                    // 方式1（类型2）:两个叶子结点都采用Merkle Tree证明
                    int c1 = std::get<0>(cost_tree[lc]) + tree_nodes[rc].size() + 8;
                    // 方式2（类型3）：左孩子采用Merkle Tree证明，右孩子采用链式证明
                    int c2 = c1;
                    // 方式3（类型4）：左孩子采用链式证明，右孩子采用Merkle Tree证明
                    int c3 = tree_nodes[rc].size() + 8 + tree_nodes[lc].size() + 8 + cost_chain[lc];
                    // 方式4（类型5）：两个孩子都采用链式证明
                    int c4 = cost_chain[lc] + 0 + tree_nodes[node_id].size() + 8;
                    
                    // 选择最小开销的方式
                    if (c1 <= c2 && c1 <= c3 && c1 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c1, 2);
                    } else if (c2 <= c1 && c2 <= c3 && c2 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c2, 3);
                    } else if (c3 <= c1 && c3 <= c2 && c3 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c3, 4);
                    } else {
                        cost_tree[node_id] = std::make_tuple(c4, 5);
                    }
                } else if (cost_chain.find(lc) == cost_chain.end() && cost_chain.find(rc) != cost_chain.end()) {
                    // 左孩子没有对应证明开销，右孩子有
                    // 方式1（类型2）:两个叶子结点都采用Merkle Tree证明
                    int c1 = tree_nodes[lc].size() + 8 + std::get<0>(cost_tree[rc]);
                    // 方式2（类型3）：左孩子采用Merkle Tree证明，右孩子采用链式证明
                    int c2 = tree_nodes[lc].size() + 8 + tree_nodes[rc].size() + 8 + cost_chain[rc];
                    // 方式3（类型4）：左孩子采用链式证明，右孩子采用Merkle Tree证明
                    int c3 = std::get<0>(cost_tree[rc]) + tree_nodes[lc].size() + 8 + 0;
                    // 方式4（类型5）：两个孩子都采用链式证明
                    int c4 = 0 + cost_chain[rc] + tree_nodes[node_id].size() + 8;
                    
                    // 选择最小开销的方式
                    if (c1 <= c2 && c1 <= c3 && c1 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c1, 2);
                    } else if (c2 <= c1 && c2 <= c3 && c2 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c2, 3);
                    } else if (c3 <= c1 && c3 <= c2 && c3 <= c4) {
                        cost_tree[node_id] = std::make_tuple(c3, 4);
                    } else {
                        cost_tree[node_id] = std::make_tuple(c4, 5);
                    }
                } else {
                    throw std::runtime_error("不应该出现的情况");
                }
            }
            
            // 将父节点加入处理队列
            if (father_ids.find(node_id) != father_ids.end() && father_ids.at(node_id) != -1) {
                int father_id = father_ids.at(node_id);
                if (processed_nodes.find(father_id) == processed_nodes.end()) {
                    node_ids_to_process.push_back(father_id);
                }
            }
        }
        
        std::cout << "  Cost Computation #node processed: " << count << " from #leafs " << subset_idx.size() << std::endl;
        return std::make_tuple(cost_tree, cost_chain);
    }

        // 构造验证对象
    MCTSubsetVerificationObject construct_vo(
        const std::unordered_map<int, std::tuple<int, int>>& cost_tree,
        const std::unordered_map<int, int>& cost_chain,
        const std::vector<int>& subset_idx) const {
        
        MCTSubsetVerificationObject vo(hash_elements.size());
        
        // 使用lambda函数递归构建VO
        std::function<void(int, bool)> recursive_construct = [&](int tree_node_id, bool chain_mode) {
            if (cost_tree.find(tree_node_id) == cost_tree.end() && cost_chain.find(tree_node_id) == cost_chain.end()) {
                // 该节点与证明生成无关，可以忽略
                return;
            }
            
            int lc = left_child_ids[tree_node_id];
            int rc = right_child_ids[tree_node_id];
            
            if (tree_node_id >= static_cast<int>(hash_elements.size())) {
                // 非叶节点
                if (chain_mode && cost_chain.find(tree_node_id) != cost_chain.end()) {
                    // 左右孩子均采用链模式生成
                    recursive_construct(lc, true);
                    if (rc != -1) {
                        recursive_construct(rc, true);
                    }
                } else if (cost_chain.find(tree_node_id) != cost_chain.end() && 
                        cost_chain.at(tree_node_id) + 8 + 32 <= std::get<0>(cost_tree.at(tree_node_id))) {
                    // 左右孩子均采用链模式生成
                    vo.add_tree_node(tree_node_id, tree_nodes[tree_node_id]);
                    recursive_construct(lc, true);
                    if (rc != -1) {
                        recursive_construct(rc, true);
                    }
                } else {
                    // 采用不同的树模式
                    int mode = std::get<1>(cost_tree.at(tree_node_id));
                    
                    if (mode == 2) {
                        // 类型2：左右孩子均采用树模式
                        if (cost_tree.find(lc) == cost_tree.end()) {
                            vo.add_tree_node(lc, tree_nodes[lc]);
                        } else {
                            recursive_construct(lc, false);
                        }
                        
                        if (rc != -1) {
                            // 存在右孩子
                            if (cost_tree.find(rc) == cost_tree.end()) {
                                vo.add_tree_node(rc, tree_nodes[rc]);
                            } else {
                                recursive_construct(rc, false);
                            }
                        }
                    } else if (mode == 3) {
                        // 类型3: 左孩子采用Merkle Tree证明，右孩子采用链式证明
                        if (cost_tree.find(lc) == cost_tree.end()) {
                            vo.add_tree_node(lc, tree_nodes[lc]);
                        } else {
                            recursive_construct(lc, false);
                        }
                        
                        if (rc != -1) {
                            vo.add_tree_node(rc, tree_nodes[rc]);
                            if (cost_chain.find(rc) != cost_chain.end()) {
                                recursive_construct(rc, true);
                            }
                        }
                    } else if (mode == 4) {
                        // 类型4：左孩子采用链式证明，右孩子采用Merkle Tree证明
                        vo.add_tree_node(lc, tree_nodes[lc]);
                        if (cost_chain.find(lc) != cost_chain.end()) {
                            recursive_construct(lc, true);
                        }
                        
                        if (rc != -1) {
                            if (cost_tree.find(rc) == cost_tree.end()) {
                                vo.add_tree_node(rc, tree_nodes[rc]);
                            } else {
                                recursive_construct(rc, false);
                            }
                        }
                    } else if (mode == 5) {
                        // 类型5：两个孩子都采用链式证明
                        vo.add_tree_node(tree_node_id, tree_nodes[tree_node_id]);
                        if (cost_chain.find(lc) != cost_chain.end()) {
                            recursive_construct(lc, true);
                        }
                        
                        if (rc != -1 && cost_chain.find(rc) != cost_chain.end()) {
                            recursive_construct(rc, true);
                        }
                    }
                }
            } else {
                // 叶节点
                if (chain_mode) {
                    // 采用链模式
                                        // 采用链模式
                    if (tree_node_id < static_cast<int>(hash_elements.size()) - 1) {
                        vo.add_chain_node(tree_nodes[tree_node_id], tree_nodes[tree_node_id + 1], chain_nodes[tree_node_id], tree_node_id);
                    } else {
                        vo.add_chain_node(tree_nodes[tree_node_id - 1], tree_nodes[tree_node_id], chain_nodes[tree_node_id - 1], tree_node_id - 1);
                    }
                } else {
                    // 采用树模式
                    vo.add_tree_node(tree_node_id, tree_nodes[tree_node_id]);
                }
            }
        };
        
        // 从根节点开始递归构建
        int root_node_id = tree_nodes.size() - 1;
        
        if (cost_chain.find(root_node_id) != cost_chain.end() && 
            cost_chain.at(root_node_id) < std::get<0>(cost_tree.at(root_node_id)) + 32) {
            // 采用全链模式
            recursive_construct(root_node_id, true);
            vo.tree_root_signature = std::vector<uint8_t>(); // 空签名表示不使用树模式
            vo.tree.clear();
        } else {
            // 采用树模式
            vo.tree_root_signature = tree_signature;
            vo.tree_num_leaf = hash_elements.size();
            recursive_construct(root_node_id, false);
        }
        
        // 优化vo结构，消除链证明中无用的区间
        std::sort(vo.chain.begin(), vo.chain.end(), 
                 [](const auto& a, const auto& b) { return std::get<0>(a) < std::get<0>(b); });
        
        std::unordered_map<int, int> used_chain_proof;
        for (size_t i = 0; i < vo.chain.size(); i++) {
            auto& t = vo.chain[i];
            int idx = std::get<3>(t);
            
            auto it = std::find(subset_idx.begin(), subset_idx.end(), idx);
            if (it != subset_idx.end() && used_chain_proof.find(idx) == used_chain_proof.end()) {
                used_chain_proof[idx] = i;
            }
            
            it = std::find(subset_idx.begin(), subset_idx.end(), idx + 1);
            if (it != subset_idx.end() && used_chain_proof.find(idx + 1) == used_chain_proof.end()) {
                used_chain_proof[idx + 1] = i;
            }
        }
        
        std::vector<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>, std::vector<uint8_t>, int>> opt_vo_chain;
        for (const auto& pair : used_chain_proof) {
            opt_vo_chain.push_back(vo.chain[pair.second]);
        }
        
        vo.chain = opt_vo_chain;
        std::sort(vo.chain.begin(), vo.chain.end(), 
                 [](const auto& a, const auto& b) { return std::get<0>(a) < std::get<0>(b); });
        
        // 验证生成的VO是否正确包含子集
        if (vo.tree_root_signature.empty()) {
            std::set<std::vector<uint8_t>> replayed_element_set;
            for (const auto& i : vo.chain) {
                replayed_element_set.insert(std::get<0>(i));
                replayed_element_set.insert(std::get<1>(i));
            }
            assert(subset_idx.size() <= replayed_element_set.size());
        }
        
        return vo;
    }

private:
    std::vector<std::vector<uint8_t>> hash_elements;   // 哈希元素列表
    std::vector<std::vector<uint8_t>> chain_nodes;     // 链节点签名
    std::vector<std::vector<uint8_t>> tree_nodes;      // 树节点哈希
    std::vector<int> left_child_ids;                  // 左孩子ID列表
    std::vector<int> right_child_ids;                 // 右孩子ID列表
    std::unordered_map<int, int> father_ids;          // 父节点ID映射
    std::vector<uint8_t> tree_signature;              // 树签名
    int prefix_len;                                   // 前缀长度
};

/**
 * 生成集合数据集的ADS
 * 对于数据集中关键词为keyword的集合S，利用pk || keyword || |S|作为验证签名密钥sk，生成该集合的MCT
 */
std::unordered_map<int, std::unordered_map<std::vector<uint8_t>, MerkleChainTree, VectorHash>> 
generate_set_intersection_ads(
    const std::unordered_map<std::vector<uint8_t>, std::vector<std::vector<uint8_t>>, VectorHash>& dataset,
    const std::vector<uint8_t>& pk,
    const std::vector<int>& prefix_lens) {
    
    std::unordered_map<int, std::unordered_map<std::vector<uint8_t>, MerkleChainTree, VectorHash>> ads;
    
    for (int prefix_len : prefix_lens) {
        std::cout << "正在处理前缀长度:" << prefix_len << std::endl;
        ads[prefix_len] = std::unordered_map<std::vector<uint8_t>, MerkleChainTree, VectorHash>();
        
        for (const auto& key_value : dataset) {
            const std::vector<uint8_t>& key = key_value.first;
            std::vector<std::vector<uint8_t>> s = key_value.second;
            
            std::sort(s.begin(), s.end());
            
            // 生成哈希值列表
            std::vector<std::vector<uint8_t>> hash_s;
            hash_s.push_back(LEFT_BOUND);
            
            for (const auto& e : s) {
                std::vector<uint8_t> hashed = sha256(e);
                hash_s.push_back(hashed);
            }
            
            hash_s.push_back(RIGHT_BOUND);
            std::sort(hash_s.begin(), hash_s.end());
            
            // 生成签名密钥sk
            std::vector<uint8_t> len_bytes(8);
            uint64_t size = hash_s.size();
            for (int i = 7; i >= 0; i--) {
                len_bytes[i] = size & 0xFF;
                size >>= 8;
            }
            
            std::vector<uint8_t> sk = pk;
            sk.push_back('|');
            sk.insert(sk.end(), key.begin(), key.end());
            sk.push_back('|');
            sk.insert(sk.end(), len_bytes.begin(), len_bytes.end());
            
            // 创建MerkleChainTree
            MerkleChainTree mct(hash_s, sk, prefix_len);
            ads[prefix_len][key] = mct;
        }
    }
    
    return ads;
}

#include <cmath>
#include <random>

/**
 * BloomFilterADS类的实现
 */
class BloomFilterADS {
public:
    BloomFilterADS(int n, float positive_rate, 
                  const std::vector<uint8_t>& left_bound,
                  const std::vector<uint8_t>& right_bound,
                  const std::vector<uint8_t>& sk,
                  const std::vector<std::vector<uint8_t>>& subset) {
        auto params = calculate_size(n, positive_rate);
        size = params.first;
        hash_count = params.second;
        
        // 创建bit数组并初始化为0
        bit_array.resize((size + 7) / 8, 0);  // 向上取整到字节
        
        generate_signature(sk, subset);
    }
    
    void generate_signature(const std::vector<uint8_t>& sk, 
                           const std::vector<std::vector<uint8_t>>& subset) {
        // 向布隆过滤器中添加元素
        for (const auto& item : subset) {
            add(item);
        }
        
        // 对bit_array进行hmac签名
        signature = hmac_sha256(sk, bit_array);
    }
    
    void add(const std::vector<uint8_t>& item) {
        for (int seed = 0; seed < hash_count; seed++) {
            int result = mmh3_hash(item, seed) % size;
            // 设置对应位为1
            bit_array[result / 8] |= (1 << (result % 8));
        }
    }
    
    bool contains(const std::vector<uint8_t>& item) const {
        for (int seed = 0; seed < hash_count; seed++) {
            int result = mmh3_hash(item, seed) % size;
            // 检查对应位是否为1
            if ((bit_array[result / 8] & (1 << (result % 8))) == 0) {
                return false;
            }
        }
        return true;
    }
    
    std::pair<int, int> calculate_size(int n, float p) {
        float m = - (n * log(p)) / (log(2) * log(2));
        float k = (m / n) * log(2);
        return std::make_pair(static_cast<int>(m), static_cast<int>(k));
    }
    
    int vo_size() const {
        return 16 + 32 + bit_array.size() + 8;
    }
    
private:
    // MurmurHash3实现
    uint32_t mmh3_hash(const std::vector<uint8_t>& key, int seed) const {
        const uint32_t c1 = 0xcc9e2d51;
        const uint32_t c2 = 0x1b873593;
        const uint32_t r1 = 15;
        const uint32_t r2 = 13;
        const uint32_t m = 5;
        const uint32_t n = 0xe6546b64;

        uint32_t hash = seed;
        
        // 处理关键字的每4个字节
        const int nblocks = key.size() / 4;
        
        // 处理主体部分
        for (int i = 0; i < nblocks; i++) {
            uint32_t k = 0;
            for (int j = 0; j < 4; j++) {
                k |= (static_cast<uint32_t>(key[i * 4 + j]) << (j * 8));
            }
            
            k *= c1;
            k = (k << r1) | (k >> (32 - r1));
            k *= c2;
            
            hash ^= k;
            hash = ((hash << r2) | (hash >> (32 - r2))) * m + n;
        }
        
        // 处理尾部
        const uint8_t* tail = key.data() + nblocks * 4;
        uint32_t k1 = 0;
        
        switch (key.size() & 3) {
            case 3: k1 ^= tail[2] << 16;
            case 2: k1 ^= tail[1] << 8;
            case 1: k1 ^= tail[0];
                    k1 *= c1; k1 = (k1 << r1) | (k1 >> (32 - r1)); k1 *= c2; hash ^= k1;
        };
        
        // Finalization
        hash ^= key.size();
        hash ^= hash >> 16;
        hash *= 0x85ebca6b;
        hash ^= hash >> 13;
        hash *= 0xc2b2ae35;
        hash ^= hash >> 16;
        
        return hash;
    }
    
    int size;
    int hash_count;
    std::vector<uint8_t> bit_array;  // bit array实现
    std::vector<uint8_t> signature;
};

/**
 * 一个集合分区的ADS
 */
class PartitionADS {
public:
    PartitionADS() : idx(-1) {}
    
    int vo_size() {
        int size = 0;
        size += 8;
        
        for (const auto& pair : mct) {
            size += pair.second.vo_size() + 8;
        }
        
        size += 8;
        for (const auto& pair : bf) {
            size += pair.second.vo_size() + 8;
        }
        
        size += 2 * 32;  // left_bound 和 right_bound
        
        return size;
    }
    
    std::unordered_map<int, MerkleChainTree> mct;  // 不同前缀长度的MCT ADS
    std::unordered_map<int, BloomFilterADS> bf;    // 不同前缀长度的BF ADS
    std::vector<uint8_t> left_bound;
    std::vector<uint8_t> right_bound;
    int idx;
};

/**
 * 为某个集合构建分区ADS
 */
std::vector<PartitionADS> construct_ads_for_set(
    const std::vector<uint8_t>& keyword,
    const std::vector<std::vector<uint8_t>>& set,
    const std::vector<uint8_t>& pk,
    const std::vector<int>& prefix_lens) {  
    std::vector<PartitionADS> result;
    return result;
}

/**
 * 集合交集计算验证对象
 */
class SetIntersectionVerificationObject {
public:
    SetIntersectionVerificationObject() : s_size(-1), r_size(-1) {}
    
    int vo_size() {
        // s_size, r_size
        int size = 16;
        
        for (const auto& pair : r_mct) {
            int l = pair.first;
            int mvo_size = pair.second.vo_size();
            std::cout << "level=" << l << ", vo_r_size=" << mvo_size << std::endl;
            size += mvo_size + 1;
        }
        
        for (const auto& pair : s_mct) {
            int l = pair.first;
            int svo_size = pair.second.vo_size();
            std::cout << "level=" << l << ", vo_s_size=" << svo_size << std::endl;
            size += svo_size + 1;
        }
        
        return size;
    }
    
    int s_size;
    int r_size;
    std::unordered_map<int, MCTSubsetVerificationObject> r_mct;
    std::unordered_map<int, MCTSubsetVerificationObject> s_mct;
};

/**
 * 服务器端：给定查询集合R和S，生成VO
 */
std::tuple<std::set<std::vector<uint8_t>, VectorCompare>, SetIntersectionVerificationObject> 
generate_set_intersection_verification_object(
    const std::unordered_map<int, std::unordered_map<std::vector<uint8_t>, MerkleChainTree, VectorHash>>& ads,
    const std::vector<int>& prefix_lens,
    const std::vector<uint8_t>& r_index,
    const std::vector<uint8_t>& s_index) {
    
    MerkleChainTree full_ads_r = ads.at(32).at(r_index);
    MerkleChainTree full_ads_s = ads.at(32).at(s_index);
    
// 修改这里（第1183行左右）
std::vector<std::vector<uint8_t>> set_r = full_ads_r.get_hash_elements();
std::vector<std::vector<uint8_t>> set_s = full_ads_s.get_hash_elements();
    
    assert(set_r.size() <= set_s.size());
    
    // 计算R ∩ S，并记录每个元素需要的最小哈希前缀长度
    std::set<std::vector<uint8_t>, VectorCompare> result;
    for (const auto& element : set_r) {
        if (std::find(set_s.begin(), set_s.end(), element) != set_s.end()) {
            result.insert(element);
        }
    }
    
    SetIntersectionVerificationObject vo;
    
    // 查找元素在有序数组中的区间
    auto find_element_interval = [](const std::vector<std::vector<uint8_t>>& s, const std::vector<uint8_t>& x) -> int {
        auto it = std::upper_bound(s.begin(), s.end(), x);
        return std::distance(s.begin(), it) - 1;
    };
    
    // 计算元素需要的最小前缀长度
    auto calculate_min_prefix_len = [](const std::vector<std::vector<uint8_t>>& s, const std::vector<uint8_t>& x, 
                                     const std::vector<int>& prefix_lens) -> int {
        auto it = std::upper_bound(s.begin(), s.end(), x);
        int i = std::distance(s.begin(), it);
        assert(i >= 1);
        
        int p = prefix_lens[0];
        for (int l : prefix_lens) {
            // 比较x与s[i-1]、s[i]的前缀，如果不相等，则返回当前前缀长度
            bool prefix_diff_prev = false;
            bool prefix_diff_next = false;
            
            if (i - 1 >= 0 && i - 1 < static_cast<int>(s.size())) {
                prefix_diff_prev = (x.size() >= l && s[i - 1].size() >= l &&
                                   std::vector<uint8_t>(x.begin(), x.begin() + l) != 
                                   std::vector<uint8_t>(s[i - 1].begin(), s[i - 1].begin() + l));
            }
            
            if (i < static_cast<int>(s.size())) {
                prefix_diff_next = (x.size() >= l && s[i].size() >= l &&
                                   std::vector<uint8_t>(x.begin(), x.begin() + l) != 
                                   std::vector<uint8_t>(s[i].begin(), s[i].begin() + l));
            }
            
            if (prefix_diff_prev && prefix_diff_next) {
                p = l;
                break;
            }
        }
        
        return p;
    };
    
    std::vector<int> r_lens;
    for (const auto& x : set_r) {
        r_lens.push_back(calculate_min_prefix_len(set_s, x, prefix_lens));
    }
    
        // 对于找到的交集元素，设置前缀长度为32（全长）
    for (size_t i = 0; i < set_r.size(); i++) {
        if (result.find(set_r[i]) != result.end()) {
            r_lens[i] = 32;
        }
    }
    
    std::cout << "计算前缀情况：最小前缀长度为：" << *std::min_element(r_lens.begin(), r_lens.end()) 
              << "，最大前缀长度为" << *std::max_element(r_lens.begin(), r_lens.end()) << std::endl;
    
    // 将|R|和|S|的信息放入VO
    vo.r_size = set_r.size();
    vo.s_size = set_s.size();
    
    // 对于每一个哈希前缀长度l
    for (int l : prefix_lens) {
        std::cout << "正在处理前缀长度:" << l << std::endl;
        
        // 检查是否有元素需要此前缀长度
        if (std::count(r_lens.begin(), r_lens.end(), l) == 0) {
            std::cout << "前缀长度" << l << "未使用，跳过" << std::endl;
            continue;
        }
        
        // 提取R子集r_l = {x|x ∈ R, L(x) = l}
        std::vector<int> r_l;
        for (size_t x = 0; x < r_lens.size(); x++) {
            if (r_lens[x] == l) {
                r_l.push_back(x);
            }
        }
        
        // 生成R子集的验证对象
        MCTSubsetVerificationObject r_mct_vo = ads.at(l).at(r_index).generate_subset_verification_object(r_l);
        vo.r_mct[l] = r_mct_vo;
        
        // 为S集合收集相关的索引
        std::set<int> s_l;
        for (int x : r_l) {
            if (std::vector<uint8_t>(set_r[x].begin(), set_r[x].begin() + l) == 
                std::vector<uint8_t>(LEFT_BOUND.begin(), LEFT_BOUND.begin() + l)) {
                s_l.insert(0);
                s_l.insert(1);
                continue;
            }
            
            if (std::vector<uint8_t>(set_r[x].begin(), set_r[x].begin() + l) == 
                std::vector<uint8_t>(RIGHT_BOUND.begin(), RIGHT_BOUND.begin() + l)) {
                s_l.insert(vo.s_size - 1);
                s_l.insert(vo.s_size - 2);
                continue;
            }
            
            int s_idx = find_element_interval(set_s, set_r[x]);
            if (s_idx >= 0 && s_idx < static_cast<int>(set_s.size()) && set_s[s_idx] == set_r[x]) {
                s_l.insert(s_idx);
            } else {
                s_l.insert(s_idx);
                if (s_idx + 1 < static_cast<int>(set_s.size())) {
                    s_l.insert(s_idx + 1);
                }
            }
        }
        
        // 将集合转换为向量并排序
        std::vector<int> s_l_vec(s_l.begin(), s_l.end());
        std::sort(s_l_vec.begin(), s_l_vec.end());
        
        // 生成S子集的验证对象
        MCTSubsetVerificationObject s_mct_vo = ads.at(l).at(s_index).generate_subset_verification_object(s_l_vec);
        vo.s_mct[l] = s_mct_vo;
    }
    
    // 将交集计算结果和VO返回用户
    return std::make_tuple(result, vo);
}

/**
 * 客户端验证集合交集计算验证对象
 */
std::tuple<bool, std::string> verify_set_intersection_vo(
    const std::vector<std::vector<uint8_t>>& result,
    const std::vector<uint8_t>& r_keywords,
    const std::vector<uint8_t>& s_keywords,
    const std::vector<uint8_t>& pk,
    const SetIntersectionVerificationObject& vo) {
    
    // 验证R的完整性
    auto verify_vo_of_r = [&]() -> std::tuple<bool, std::string, std::set<std::vector<uint8_t>, VectorCompare>> {
        // 对于每个哈希前缀长度l，根据私钥pk、R的关键词keyword，校验VO.R[l]的签名
        std::set<std::vector<uint8_t>, VectorCompare> replayed_r;
        
        for (const auto& pair : vo.r_mct) {
            int l = pair.first;
            const MCTSubsetVerificationObject& r_mct = pair.second;
            
            std::cout << "验证R集合VO前缀" << l << "." << std::endl;
            
            // 生成签名密钥
            std::vector<uint8_t> size_bytes(8);
            uint64_t size = vo.r_size;
            for (int i = 7; i >= 0; i--) {
                size_bytes[i] = size & 0xFF;
                size >>= 8;
            }
            
            std::vector<uint8_t> sk = pk;
            sk.push_back('|');
            sk.insert(sk.end(), r_keywords.begin(), r_keywords.end());
            sk.push_back('|');
            sk.insert(sk.end(), size_bytes.begin(), size_bytes.end());
            
            // 验证
            std::vector<std::vector<uint8_t>> empty_query;
            auto verify_result = r_mct.verify(sk, empty_query);
            
            bool flag = std::get<0>(verify_result);
            if (!flag) {
                std::string msg = "R集合前缀" + std::to_string(l) + "验证失败.";
                std::cout << msg << std::endl;
                return std::make_tuple(false, msg, std::set<std::vector<uint8_t>, VectorCompare>());
            }
            
            // 收集元素
            const auto& r_l = std::get<1>(verify_result);
            replayed_r.insert(r_l.begin(), r_l.end());
        }
        
        // 合并replayed_r中出现的元素（消除所有的低前缀长度子串）
        std::vector<std::vector<uint8_t>> tmp_l(replayed_r.begin(), replayed_r.end());
        std::sort(tmp_l.begin(), tmp_l.end());
        
        for (size_t i = 0; i < tmp_l.size() - 1; i++) {
            size_t len = tmp_l[i].size();
            if (len <= tmp_l[i + 1].size() && 
                std::equal(tmp_l[i].begin(), tmp_l[i].end(), tmp_l[i + 1].begin())) {
                replayed_r.erase(tmp_l[i]);
            }
        }
        
        // 验证大小是否匹配
        if (replayed_r.size() != vo.r_size) {
            std::string msg = "R集合长度验证失败, 预期长度" + std::to_string(vo.r_size) + 
                             "，实际获得长度" + std::to_string(replayed_r.size());
            std::cout << msg << std::endl;
            return std::make_tuple(false, msg, std::set<std::vector<uint8_t>, VectorCompare>());
        }
        
        return std::make_tuple(true, "", replayed_r);
    };
    
    // 验证S的完整性
    auto verify_vo_of_s = [&]() -> std::tuple<bool, std::string, 
                                             std::set<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>>> {
        std::set<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>> replayed_s_intervals;
        
        for (const auto& pair : vo.s_mct) {
            int l = pair.first;
            const MCTSubsetVerificationObject& s_mct = pair.second;
            
            std::cout << "验证S集合VO前缀" << l << "." << std::endl;
            
            // 生成签名密钥
            std::vector<uint8_t> size_bytes(8);
            uint64_t size = vo.s_size;
            for (int i = 7; i >= 0; i--) {
                size_bytes[i] = size & 0xFF;
                size >>= 8;
            }
            
            std::vector<uint8_t> sk = pk;
            sk.push_back('|');
            sk.insert(sk.end(), s_keywords.begin(), s_keywords.end());
            sk.push_back('|');
            sk.insert(sk.end(), size_bytes.begin(), size_bytes.end());
            
            // 验证
            std::vector<std::vector<uint8_t>> empty_query;
            auto verify_result = s_mct.verify(sk, empty_query);
            
            bool flag = std::get<0>(verify_result);
            if (!flag) {
                std::string msg = "S集合前缀" + std::to_string(l) + "验证失败.";
                std::cout << msg << std::endl;
                return std::make_tuple(false, msg, std::set<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>>());
            }
            
            // 从VO_Chain中提取连续的子集区间S'
            std::unordered_map<int, std::vector<uint8_t>> known_leafs;
            for (const auto& tuple : s_mct.chain) {
                known_leafs[std::get<3>(tuple)] = std::get<0>(tuple);
                known_leafs[std::get<3>(tuple) + 1] = std::get<1>(tuple);
            }
            
            // 从VO_Tree中提取叶节点
            for (const auto& node_pair : s_mct.tree) {
                int node_id = node_pair.first;
                if (node_id < vo.s_size) {
                    known_leafs[node_id] = node_pair.second;
                }
            }
            
            // 构建区间
            for (const auto& node_pair : known_leafs) {
                int node_id = node_pair.first;
                const std::vector<uint8_t>& node_val = node_pair.second;
                
                if (known_leafs.find(node_id + 1) != known_leafs.end()) {
                    replayed_s_intervals.insert(std::make_tuple(node_val, known_leafs[node_id + 1]));
                }
                
                if (node_id + 1 == vo.s_size - 1) {
                    std::vector<uint8_t> right_bound_prefix(RIGHT_BOUND.begin(), 
                                                           RIGHT_BOUND.begin() + std::min(l, static_cast<int>(RIGHT_BOUND.size())));
                    replayed_s_intervals.insert(std::make_tuple(node_val, right_bound_prefix));
                }
            }
        }
        
        return std::make_tuple(true, "", replayed_s_intervals);
    };
    
    // 验证交集
    auto verify_intersection = [](const std::vector<std::vector<uint8_t>>& result,
                                 const std::set<std::vector<uint8_t>, VectorCompare>& replayed_r,
                                 const std::set<std::tuple<std::vector<uint8_t>, std::vector<uint8_t>>>& replayed_s_intervals) 
                              -> std::tuple<bool, std::string> {
        // 对于R'中的每个元素x
        for (const auto& x : replayed_r) {
            std::tuple<std::vector<uint8_t>, std::vector<uint8_t>> s_tuple;
            bool found_interval = false;
            int max_prefix_len = 0;
            
            for (const auto& t : replayed_s_intervals) {
                const std::vector<uint8_t>& t_start = std::get<0>(t);
                const std::vector<uint8_t>& t_end = std::get<1>(t);
                
                if (t_start <= x && x <= t_end) {
                    int prefix_len = std::min(t_start.size(), t_end.size());
                    
                    if (!found_interval || prefix_len > max_prefix_len) {
                        s_tuple = t;
                        found_interval = true;
                        max_prefix_len = prefix_len;
                    }
                }
            }
            
            if (!found_interval) {
                std::string msg = "元素未在S集合中找出覆盖区间.";
                std::cout << msg << std::endl;
                return std::make_tuple(false, msg);
            }
            
            const std::vector<uint8_t>& s_tuple_start = std::get<0>(s_tuple);
            const std::vector<uint8_t>& s_tuple_end = std::get<1>(s_tuple);
            
            if (x == s_tuple_start || x == s_tuple_end) {
                // 元素应该在交集中
                auto it = std::find(result.begin(), result.end(), x);
                if (it == result.end()) {
                    std::string msg = "元素应该在交集中出现，但未出现在计算结果中.";
                    std::cout << msg << std::endl;
                    return std::make_tuple(false, msg);
                }
            } else {
                // 元素不应该在交集中
                auto it = std::find(result.begin(), result.end(), x);
                if (it != result.end()) {
                    std::string msg = "元素不应该在交集中出现，但出现在计算结果中.";
                    std::cout << msg << std::endl;
                    return std::make_tuple(false, msg);
                }
            }
        }
        
        return std::make_tuple(true, "验证通过");
    };
    
    // 执行验证流程
    auto r_result = verify_vo_of_r();
    bool flag = std::get<0>(r_result);
    if (!flag) {
        return std::make_tuple(flag, std::get<1>(r_result));
    }
    
        auto s_result = verify_vo_of_s();
    flag = std::get<0>(s_result);
    if (!flag) {
        return std::make_tuple(flag, std::get<1>(s_result));
    }
    
    auto intersection_result = verify_intersection(result, std::get<2>(r_result), std::get<2>(s_result));
    return intersection_result;
}

// ########### 测试代码部分 ###########

void test_subset_verification() {
    // 子集验证的代码
    // 生成长度为10和20的随机整数集合R和S
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<> dis(1, 10000);
    
    // 生成长度为10的随机整数集合R
    std::set<int> R;
    while (R.size() < 10) {
        R.insert(dis(gen));
    }
    std::vector<std::vector<uint8_t>> hashR;
    hashR.push_back(LEFT_BOUND);
    for (int e : R) {
        std::vector<uint8_t> e_bytes(sizeof(int));
        std::memcpy(e_bytes.data(), &e, sizeof(int));
        hashR.push_back(sha256(e_bytes));
    }
    hashR.push_back(RIGHT_BOUND);
    std::sort(hashR.begin(), hashR.end());
    
    // 生成长度为20的随机整数集合S
    std::set<int> S;
    while (S.size() < 20) {
        S.insert(dis(gen));
    }
    std::vector<std::vector<uint8_t>> hashS;
    hashS.push_back(LEFT_BOUND);
    for (int e : S) {
        std::vector<uint8_t> e_bytes(sizeof(int));
        std::memcpy(e_bytes.data(), &e, sizeof(int));
        hashS.push_back(sha256(e_bytes));
    }
    hashS.push_back(RIGHT_BOUND);
    std::sort(hashS.begin(), hashS.end());
    
    // 生成长度为1000的随机整数集合big_R
    std::set<int> big_R;
    while (big_R.size() < 1000) {
        big_R.insert(dis(gen));
    }
    std::vector<std::vector<uint8_t>> hash_bigR;
    hash_bigR.push_back(LEFT_BOUND);
    for (int e : big_R) {
        std::vector<uint8_t> e_bytes(sizeof(int));
        std::memcpy(e_bytes.data(), &e, sizeof(int));
        hash_bigR.push_back(sha256(e_bytes));
    }
    hash_bigR.push_back(RIGHT_BOUND);
    std::sort(hash_bigR.begin(), hash_bigR.end());
    
    // 测试Merkle Chain Tree结构生成
    std::vector<uint8_t> sk(32, 0x01);
    MerkleChainTree treeR4(hashR, sk, 32);
    MerkleChainTree treeS4(hashS, sk, 32);
    
    // 循环自动测试
    const int PREFIX_LEN = 4;
    MerkleChainTree treeBigR(hash_bigR, sk, PREFIX_LEN);
    
    for (size_t slen = 1; slen < big_R.size(); slen++) {
        for (int i = 0; i < 100; i++) {
            // 随机选择索引
            std::vector<int> pick_index;
            std::uniform_int_distribution<> index_dis(0, hash_bigR.size() - 1);
            while (pick_index.size() < slen) {
                int idx = index_dis(gen);
                if (std::find(pick_index.begin(), pick_index.end(), idx) == pick_index.end()) {
                    pick_index.push_back(idx);
                }
            }
            
            // 从选中的索引中提取前缀
            std::set<std::vector<uint8_t>, VectorCompare> pickset;
            for (int x : pick_index) {
                if (x < hash_bigR.size()) {
                    pickset.insert(std::vector<uint8_t>(hash_bigR[x].begin(), hash_bigR[x].begin() + PREFIX_LEN));
                }
            }
            
            // 生成并验证子集验证对象
            MCTSubsetVerificationObject voBigR = treeBigR.generate_subset_verification_object(pick_index);
            auto [flag, subset, set_ranges] = voBigR.verify(sk, std::vector<std::vector<uint8_t>>(pickset.begin(), pickset.end()));
            
            // 验证结果
            std::set<std::vector<uint8_t>, VectorCompare> subset_set(subset.begin(), subset.end());
            std::set<std::vector<uint8_t>, VectorCompare> intersection;
            std::set_intersection(
                pickset.begin(), pickset.end(),
                subset_set.begin(), subset_set.end(),
                std::inserter(intersection, intersection.begin()),
                VectorCompare()
            );
            
            assert(flag && intersection.size() == pickset.size());
            
            // 修改VO并验证是否能检测出篡改
            MCTSubsetVerificationObject modifiedVO = voBigR;
            if (!modifiedVO.tree.empty()) {
                // 从modifiedVO.tree中随机选取一个元素删除
                auto it = modifiedVO.tree.begin();
                std::advance(it, rand() % modifiedVO.tree.size());
                modifiedVO.tree.erase(it);
            }
            if (!modifiedVO.chain.empty()) {
                // 从modifiedVO.chain中随机选取一个元素删除
                modifiedVO.chain.erase(modifiedVO.chain.begin() + rand() % modifiedVO.chain.size());
            }
            
            auto [mod_flag, mod_subset, mod_set_ranges] = modifiedVO.verify(sk, std::vector<std::vector<uint8_t>>(pickset.begin(), pickset.end()));
            
            std::set<std::vector<uint8_t>, VectorCompare> mod_subset_set(mod_subset.begin(), mod_subset.end());
            std::set<std::vector<uint8_t>, VectorCompare> mod_intersection;
            std::set_intersection(
                pickset.begin(), pickset.end(),
                mod_subset_set.begin(), mod_subset_set.end(),
                std::inserter(mod_intersection, mod_intersection.begin()),
                VectorCompare()
            );
            
            if (mod_intersection.size() != pickset.size()) {
                std::cout << "结果被篡改，正在校验是否能检测出" << std::endl;
                assert(mod_flag == false);
            }
        }
    }
}

void test_mct_example() {
    // 测试具体的例子
    std::vector<int> s = {482, 451, 456, 714, 554, 779, 653, 495, 497, 83, 56, 123, 732};
    std::vector<int> sub_idx = {1, 2, 4, 5, 7, 8};
    
    std::vector<std::vector<uint8_t>> hash_s;
    hash_s.push_back(LEFT_BOUND);
    for (int e : s) {
        std::vector<uint8_t> e_bytes(sizeof(int));
        std::memcpy(e_bytes.data(), &e, sizeof(int));
        hash_s.push_back(sha256(e_bytes));
    }
    hash_s.push_back(RIGHT_BOUND);
    std::sort(hash_s.begin(), hash_s.end());
    
    std::vector<uint8_t> sk(32, 0x01);
    MerkleChainTree mct(hash_s, sk, 32);
    MCTSubsetVerificationObject vo = mct.generate_subset_verification_object(sub_idx);
    
    // 打印验证对象
    std::cout << "验证对象: 树节点数=" << vo.tree.size() << ", 链长度=" << vo.chain.size() << std::endl;
}

void test_set_intersection_verification() {
    // 测试MCT的生成和验证功能
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<> dis(1, 10000);
    
    std::vector<int> keys = {1, 2, 3};
    std::unordered_map<std::vector<uint8_t>, std::vector<std::vector<uint8_t>>, VectorHash> sets;
    
    std::vector<int> set1 = {768, 649, 137, 907, 15, 916, 789, 277, 24, 921, 26, 157, 933, 808, 426, 428, 45, 692, 567, 441, 826, 960, 706, 836, 709, 580, 456, 210, 217, 860, 608, 483, 612, 997, 886, 762, 763, 892, 382, 383};
    std::vector<int> set2 = {768, 384, 386, 6, 264, 779, 528, 532, 281, 154, 30, 927, 928, 929, 39, 427, 689, 947, 308, 445, 701, 62, 833, 579, 453, 197, 715, 846, 336, 211, 856, 601, 220, 488, 106, 110, 116, 117, 759, 764, 510};
    
    std::vector<std::vector<uint8_t>> set1_bytes;
    std::vector<std::vector<uint8_t>> set2_bytes;
    
    for (int e : set1) {
        std::vector<uint8_t> e_bytes(sizeof(int));
        std::memcpy(e_bytes.data(), &e, sizeof(int));
        set1_bytes.push_back(e_bytes);
    }
    
    for (int e : set2) {
        std::vector<uint8_t> e_bytes(sizeof(int));
        std::memcpy(e_bytes.data(), &e, sizeof(int));
        set2_bytes.push_back(e_bytes);
    }
    
    sets[{1}] = set1_bytes;
    sets[{2}] = set2_bytes;
    
    std::vector<int> prefix_lens = {4, 32};
    std::vector<uint8_t> pk(32, 0x01);
    
    auto ads = generate_set_intersection_ads(sets, pk, prefix_lens);
    std::cout << "ADS已建立" << std::endl;
    
    auto result_tuple = generate_set_intersection_verification_object(ads, prefix_lens, {1}, {2});
    auto result = std::get<0>(result_tuple);
    auto vo = std::get<1>(result_tuple);
    
    std::cout << "交集大小: " << result.size() << std::endl;
    
    std::vector<std::vector<uint8_t>> result_vec(result.begin(), result.end());
    auto verify_result = verify_set_intersection_vo(result_vec, {1}, {2}, pk, vo);
    
    if (std::get<0>(verify_result)) {
        std::cout << "验证通过" << std::endl;
    } else {
        std::cout << "验证失败: " << std::get<1>(verify_result) << std::endl;
    }
}

void test_random_set_intersection() {
    // 随机测试MCT的生成和验证功能
    std::random_device rd;
    std::mt19937 gen(rd());
    
    for (int i = 0; i < 20; i++) {  
        // 随机生成两个长度在5~1000之间的集合s1和s2
        std::uniform_int_distribution<> size_dis1(5, 100);  
        std::uniform_int_distribution<> size_dis2(5, 100);
        std::uniform_int_distribution<> elem_dis(1, 10000);
        
        int s1_size = size_dis1(gen);
        int s2_size = size_dis2(gen);
        
        std::set<int> s1;
        while (s1.size() < s1_size) {
            s1.insert(elem_dis(gen));
        }
        
        std::set<int> s2;
        while (s2.size() < s2_size) {
            s2.insert(elem_dis(gen));
        }
        
        // 交换s1和s2如果s1的规模较大
        if (s1.size() > s2.size()) {
            std::swap(s1, s2);
        }
        
        // 生成ADS
        std::unordered_map<std::vector<uint8_t>, std::vector<std::vector<uint8_t>>, VectorHash> sets;
        std::vector<std::vector<uint8_t>> s1_bytes, s2_bytes;
        
        for (int e : s1) {
            std::vector<uint8_t> e_bytes(sizeof(int));
            std::memcpy(e_bytes.data(), &e, sizeof(int));
            s1_bytes.push_back(e_bytes);
        }
        
        for (int e : s2) {
            std::vector<uint8_t> e_bytes(sizeof(int));
            std::memcpy(e_bytes.data(), &e, sizeof(int));
            s2_bytes.push_back(e_bytes);
        }
        
        std::vector<uint8_t> key1 = {1};
        std::vector<uint8_t> key2 = {2};
        
        sets[key1] = s1_bytes;
        sets[key2] = s2_bytes;
        
        std::vector<int> prefix_lens = {4, 32};
        std::vector<uint8_t> pk(32, 0x01);
        
        auto ads = generate_set_intersection_ads(sets, pk, prefix_lens);
        std::cout << "ADS已建立, |R| = " << s1.size() << " & |S| = " << s2.size() << std::endl;
        
        auto result_tuple = generate_set_intersection_verification_object(ads, prefix_lens, key1, key2);
        auto result = std::get<0>(result_tuple);
        auto vo = std::get<1>(result_tuple);
        
        std::vector<std::vector<uint8_t>> result_vec(result.begin(), result.end());
        auto verify_result = verify_set_intersection_vo(result_vec, key1, key2, pk, vo);
        
        assert(std::get<0>(verify_result) == true);
        std::cout << "验证通过" << std::endl;
        
        if (result.size() > 2) {
            std::vector<std::vector<uint8_t>> modified_result(result_vec);
            std::sort(modified_result.begin(), modified_result.end());
            
                       // 从modified_result中随机选择一个元素删除
            if (!modified_result.empty()) {
                std::uniform_int_distribution<> elem_idx_dis(0, modified_result.size() - 1);
                int idx_to_remove = elem_idx_dis(gen);
                modified_result.erase(modified_result.begin() + idx_to_remove);
                
                auto mod_verify_result = verify_set_intersection_vo(modified_result, key1, key2, pk, vo);
                std::cout << "数据已篡改，正在检测篡改是否能被验证" << std::endl;
                assert(std::get<0>(mod_verify_result) == false);
            }
        }
    }
}

void test_performance() {
    // 测试性能
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<> dis(1, 5000000);
    
    std::unordered_map<std::vector<uint8_t>, std::vector<std::vector<uint8_t>>, VectorHash> sets;
    
    // 生成100个元素的集合
    std::vector<std::vector<uint8_t>> set1_bytes;
    for (int i = 0; i < 100; i++) {
        int val = dis(gen);
        std::vector<uint8_t> e_bytes(sizeof(int));
        std::memcpy(e_bytes.data(), &val, sizeof(int));
        set1_bytes.push_back(e_bytes);
    }
    
    // 生成1000个元素的集合
    std::vector<std::vector<uint8_t>> set2_bytes;
    for (int i = 0; i < 1000; i++) {
        int val = dis(gen);
        std::vector<uint8_t> e_bytes(sizeof(int));
        std::memcpy(e_bytes.data(), &val, sizeof(int));
        set2_bytes.push_back(e_bytes);
    }
    
    std::vector<uint8_t> key1 = {1};
    std::vector<uint8_t> key2 = {2};
    
    sets[key1] = set1_bytes;
    sets[key2] = set2_bytes;
    
    std::vector<int> prefix_lens = {4, 32};
    std::vector<uint8_t> pk(32, 0x01);
    
    // 计时开始
    auto start = std::chrono::high_resolution_clock::now();
    
    auto ads = generate_set_intersection_ads(sets, pk, prefix_lens);
    std::cout << "ADS已建立" << std::endl;
    
    auto result_tuple = generate_set_intersection_verification_object(ads, prefix_lens, key1, key2);
    auto result = std::get<0>(result_tuple);
    auto vo = std::get<1>(result_tuple);
    
    std::cout << "交集元素数量: " << result.size() << std::endl;
    
    std::vector<std::vector<uint8_t>> result_vec(result.begin(), result.end());
    auto verify_result = verify_set_intersection_vo(result_vec, key1, key2, pk, vo);
    
    // 计时结束
    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> elapsed = end - start;
    
    std::cout << "VO大小: " << vo.vo_size() << " bytes" << std::endl;
    std::cout << "执行时间: " << elapsed.count() << " 秒" << std::endl;
    
    if (std::get<0>(verify_result)) {
        std::cout << "验证成功: " << std::get<1>(verify_result) << std::endl;
    } else {
        std::cout << "验证失败: " << std::get<1>(verify_result) << std::endl;
    }
}

int main() {
    
    
    // 测试子集验证
    // test_subset_verification();
    
    // 测试特定示例
    // test_mct_example();
    
    // 测试集合交集验证
    // test_set_intersection_verification();
    
    // 随机测试集合交集验证
    // test_random_set_intersection();
    
    // 测试性能
    test_performance();
    
    return 0;
}