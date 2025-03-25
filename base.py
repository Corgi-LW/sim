#!/usr/bin/env python3

# 实现Partitioned Merkle Chain Tree结构

# %%

from collections import deque
from typing import Dict, List, Set, Tuple
from hashlib import sha256
import hmac
from bisect import bisect_right
#from line_profiler import profile


# LEFT_BOUND等于32个字节的0构成的bytes
LEFT_BOUND = b'\x00' * 32
# RIGHT_BOUND等于32个字节的0xFF构成的bytes
RIGHT_BOUND = b'\xFF' * 32


class MCTSubsetVerificationObject:
    """基于MCT的子集存在性验证对象VO。
    VO由VO_Chain和VO_Tree两部分组成，并且在递归调用的过程中全程维护。
        - VO_Chain: [(HASH, HASH_next, ChainNodeSig)]
        - VO_Tree: (Nodes: NodeID:Long-> HASH, RootNodeSignature:HASH, NumLeaf:Long)
    """
    def __init__(self, num_element_in_set:int):
        """
        num_element_in_set: 集合S中元素的数量
        """
        self.chain:List[Tuple[bytes, bytes, bytes, int]] = []
        self.tree:Dict[int, bytes] = {}
        self.tree_root_signature:bytes = None
        self.tree_num_leaf:int = num_element_in_set

    def add_chain_node(self, element:bytes, next_element:bytes, chain_node_signature:bytes, idx:int):
        """添加一个链式证明节点"""
        self.chain.append((element, next_element, chain_node_signature, idx))
    def add_tree_node(self, node_id:int, hash:bytes):
        """添加一个树状证明节点"""
        self.tree[node_id] = hash
    def verify(self, sk:bytes, query_subset:List[bytes]) -> Tuple[bool, List[bytes], List[Tuple[bytes, bytes]]]:
        """验证VO"""
        """
        在Client端，对于一个子集$s$的验证对象$VO$，按照以下的方式进行校验：
        * 如果VO中不包含VO_Tree（即采用全链模式），
            - 重算VO_Chain中每一个Tuple的ChainNodeSig值.
            - 如果所有的ChainNodeSig都正确，则验证通过。VO_Chain中每个Tuple的所有HASH都是子集$s$元素。
        * 如果VO包含VO_Tree（即采用树状验证模式），
            - 根据VO_Tree.NumLeaf值，计算Merkle Hash Tree的层数以及每一层的节点数、起始ID。
            - 先验证VO_Chain中所有Tuple。VO_Chain中的每个Tuple的HASH都是子集$s$的元素。
            - 采用递归的方式，从根节点ID开始自顶向下的验证，并计算根节点的哈希值。
                + 对于每一个非叶节点$T$，
                    - 如果VO_Tree.Nodes中包含T的哈希值（类型5），返回T的哈希值。
                    - 如果VO_Tree.Nodes中包含右孩子哈希值，递归计算左孩子哈希值，计算本结点哈希值。
                    - 如果VO_Tree.Nodes中包含左孩子哈希值，递归计算右孩子哈希值，计算本结点哈希值。
                    - 如果VO_Tree.Nodes中不包含左孩子哈希值与右孩子哈希值，递归计算左孩子哈希值与右孩子哈希值，计算本结点哈希值。
                + 对于每一个叶节点$T$，
                    - 如果VO_Tree.Nodes中包含T的哈希值，返回T的哈希值。
                    - 否则，验证失败，返回一个全0的哈希值。
            - 根据递归计算出的根结点哈希值，签名后与VO_Tree.RootNodeSignature进行验证。如果验证通过，则完备性验证通过。VO_Tree.Nodes中所有叶结点的哈希值都为子集$s$的元素。
        """
        if self.tree_root_signature is None:
            # 不包含VO_Tree的情况，采用全链模式
            if len(self.chain) == 0:
                return False, [], []
            set_ranges = []
            subset = []
            for t in self.chain:
                element, next_element, chain_node_signature, idx = t
                key = element + b'|' + next_element + b'|' + idx.to_bytes(8, 'big')
                signature = hmac.new(sk, key, digestmod=sha256).digest()
                if signature != chain_node_signature:
                    print("链节点验证失败")
                    return False, [], []
                set_ranges.append((element, next_element))
                subset.append(element)
                subset.append(next_element)
            subset = list(set(subset))
            subset.sort()
            for e in query_subset:
                if e not in set(subset):
                    print("子集验证失败，元素不存在")
                    return False, subset, set_ranges
            return True, subset, set_ranges
        else:
            # 包含VO_Tree的情况，采用树状模式
            # 根据self.tree_num_leaf值，计算Merkle Hash Tree的层数、左右孩子index、父节点index
            def build_tree_structure(num_leaf) -> Tuple[List[int], List[int], Dict[int, int]]:
                # 构建Merkle哈希树结构
                left_child_ids = [] # 记录每个节点左孩子的ID
                right_child_ids = [] # 记录每个节点右孩子的ID
                father_ids = {} # 记录每个节点的父节点ID
                tree_nodes = []
                for i in range(num_leaf):
                    tree_nodes.append(1)
                    left_child_ids.append(-1)
                    right_child_ids.append(-1)
                nodes_to_process = tree_nodes.copy()
                new_nodes = []
                current_node_id = 0
                while len(nodes_to_process) > 1:
                    for i in range(0, len(nodes_to_process), 2):
                        if i + 1 < len(nodes_to_process):
                            new_nodes.append(1)
                            left_child_ids.append(current_node_id)
                            right_child_ids.append(current_node_id+1)
                            father_ids[current_node_id] = len(tree_nodes) + len(new_nodes) - 1
                            father_ids[current_node_id+1] = len(tree_nodes) + len(new_nodes) - 1
                            current_node_id += 2
                        else:
                            new_nodes.append(nodes_to_process[i])
                            left_child_ids.append(current_node_id)
                            right_child_ids.append(-1)
                            father_ids[current_node_id] = len(tree_nodes) + len(new_nodes) - 1
                            current_node_id += 1
                    tree_nodes.extend(new_nodes)
                    nodes_to_process = new_nodes
                    new_nodes = []
                assert current_node_id == len(tree_nodes) - 1
                # 此时所有的结点都已经计算完毕，存储在tree_nodes中
                father_ids[len(tree_nodes)-1] = -1 # 根节点没有父节点
                return left_child_ids, right_child_ids, father_ids
            left_child_ids, right_child_ids, father_ids = build_tree_structure(self.tree_num_leaf)
            # 先验证VO_Chain中所有Tuple。VO_Chain中的每个Tuple的HASH都是子集$s$的元素。
            for t in self.chain:
                element, next_element, chain_node_signature, idx = t
                key = element + b'|' + next_element + b'|' + idx.to_bytes(8, 'big')
                signature = hmac.new(sk, key, digestmod=sha256).digest()
                if signature != chain_node_signature:
                    print("链节点验证失败")
                    return False, [], []
            # 采用递归的方式，从根节点ID开始自顶向下的验证，并计算根节点的哈希值。
            def reconstruct_tree_root_hash(tree_node_id:int) -> bytes:
                lc = left_child_ids[tree_node_id]
                rc = right_child_ids[tree_node_id]
                if tree_node_id >= self.tree_num_leaf:
                    # 非叶节点
                    #如果VO_Tree.Nodes中包含T的哈希值（类型5），返回T的哈希值。
                    if tree_node_id in self.tree:
                        return self.tree[tree_node_id]
                    if rc == -1:
                        # 如果没有右孩子
                        return reconstruct_tree_root_hash(lc)
                    #如果VO_Tree.Nodes中包含右孩子哈希值，递归计算左孩子哈希值，计算本结点哈希值。
                    if rc in self.tree:
                        lc_hash = reconstruct_tree_root_hash(lc)
                        if lc_hash is None:
                            return None
                        rc_hash = self.tree[rc]
                        my_hash = sha256(lc_hash + b'|' +  rc_hash).digest()
                        return my_hash
                    #如果VO_Tree.Nodes中包含左孩子哈希值，递归计算右孩子哈希值，计算本结点哈希值。
                    if lc in self.tree:
                        lc_hash = self.tree[lc]
                        rc_hash = reconstruct_tree_root_hash(rc)
                        if rc_hash is None:
                            return None
                        my_hash = sha256(lc_hash + b'|' +  rc_hash).digest()
                        return my_hash
                    #如果VO_Tree.Nodes中不包含左孩子哈希值与右孩子哈希值，递归计算左孩子哈希值与右孩子哈希值，计算本结点哈希值。
                    if lc not in self.tree and rc not in self.tree:
                        lc_hash = reconstruct_tree_root_hash(lc)
                        if lc_hash is None:
                            return None
                        rc_hash = reconstruct_tree_root_hash(rc)
                        if rc_hash is None:
                            return None
                        my_hash = sha256(lc_hash + b'|' +  rc_hash).digest()
                        return my_hash
                    print(f"出现了意外的情况，无法计算中间节点{tree_node_id}的哈希值")
                    return None
                else:
                    # 叶节点
                    if tree_node_id in self.tree:
                        return self.tree[tree_node_id]
                    else:
                        # 如果VO_Tree.Nodes中不包含T的哈希值（类型5），返回None。
                        print(f"出现了意外的情况，无法获得叶节点{tree_node_id}的哈希值")
                        return None
            root_node_hash = reconstruct_tree_root_hash(len(left_child_ids)-1)
            print(root_node_hash)
            root_signature = hmac.new(sk, root_node_hash, digestmod=sha256).digest()
            if root_signature != self.tree_root_signature:
                print("根节点签名验证失败")
                return False, [], []
            # 验证通过，对集合区间进行回放
            subset = []
            set_ranges = []
            for t in self.chain:
                element, next_element, chain_node_signature, idx = t
                subset.append(element)
                subset.append(next_element)
                set_ranges.append((element, next_element))
            for tree_node_id in self.tree.keys():
                if tree_node_id >= self.tree_num_leaf:
                    continue # 跳过非叶节点
                subset.append(self.tree[tree_node_id])
                if tree_node_id < self.tree_num_leaf - 1 and tree_node_id + 1 in self.tree:
                    set_ranges.append((self.tree[tree_node_id], self.tree[tree_node_id + 1]))
            subset = list(set(subset))
            subset.sort()
            set_ranges = list(set(set_ranges))
            set_ranges.sort()
            for e in query_subset:
                if e not in set(subset):
                    print("子集验证失败，元素不存在")
                    return False, subset, set_ranges
            return True, subset, set_ranges

    def vo_size(self)->int:
        # level
        size = 8
        #self.chain:List[Tuple[bytes, bytes, bytes]] = []
        size += 8
        for t in self.chain:
            element, next_element, chain_node_signature, idx = t
            size += len(element) + len(next_element) + len(chain_node_signature) + 8
        #self.tree:Dict[int, bytes] = {}
        size += 8
        for tree_node_id in self.tree.keys():
            size += len(self.tree[tree_node_id])
        # self.tree_root_signature
        size += 32
        #self.tree_num_leaf:int = num_element_in_set
        size += 8
        return size

class MerkleChainTree:
    def __init__(self, hash_elements:List[bytes], sk:bytes, prefix_len:int):
        """要求传入的hash_elments列表是带有边界值的列表"""
        assert hash_elements[0] == LEFT_BOUND
        assert hash_elements[-1] == RIGHT_BOUND
        self.hash_elements:List[bytes] = []
        for e in hash_elements:
            self.hash_elements.append(e[0:prefix_len])
        self.hash_elements.sort() # 带有边界值的元素数量
        self.chain_nodes:List[bytes] = self.build_chain_nodes(sk)
        self.tree_nodes, self.left_child_ids, self.right_child_ids, self.father_ids = self.build_tree_nodes(sk)
        #print(f"根节点哈希值:{self.tree_nodes[-1]}")
        self.tree_signature:bytes = hmac.new(sk, self.tree_nodes[-1], digestmod=sha256).digest()
        self.prefix_len = prefix_len
        
    def vo_size(self)->int:
        size = 0
        size += 8
        for h in self.hash_elements:
            size += len(h)
        size += 32 * len(self.chain_nodes)
        for t in self.tree_nodes:
            size += len(t)
        size += len(self.tree_signature)
        size += 8 # prefix_len
        return size

    def build_chain_nodes(self, sk:bytes) -> List[bytes]:
        # 构建Chain验证签名结点
        chain_nodes = []
        for i in range(len(self.hash_elements) - 1):
            # 计算e的签名
            key = self.hash_elements[i] + b'|' + self.hash_elements[i+1] + b'|' + i.to_bytes(8, 'big')
            signature = hmac.new(sk, key, digestmod=sha256).digest()
            chain_nodes.append(signature)
        return chain_nodes

    def build_tree_nodes(self, sk:bytes) -> Tuple[List[bytes], List[int], List[int], Dict[int, int]]:
        # 构建Merkle哈希树结点
        tree_nodes = []
        left_child_ids = [] # 记录每个节点左孩子的ID
        right_child_ids = [] # 记录每个节点右孩子的ID
        father_ids = {} # 记录每个节点的父节点ID
        for i in range(len(self.hash_elements)):
            tree_nodes.append(self.hash_elements[i])
            left_child_ids.append(-1)
            right_child_ids.append(-1)
        nodes_to_process = tree_nodes.copy()
        new_nodes = []
        current_node_id = 0
        while len(nodes_to_process) > 1:
            for i in range(0, len(nodes_to_process), 2):
                if i + 1 < len(nodes_to_process):
                    key = nodes_to_process[i] + b'|' + nodes_to_process[i+1]
                    new_node = sha256(key).digest()
                    new_nodes.append(new_node)
                    left_child_ids.append(current_node_id)
                    right_child_ids.append(current_node_id+1)
                    father_ids[current_node_id] = len(tree_nodes) + len(new_nodes) - 1
                    father_ids[current_node_id+1] = len(tree_nodes) + len(new_nodes) - 1
                    current_node_id += 2
                else:
                    new_nodes.append(nodes_to_process[i])
                    left_child_ids.append(current_node_id)
                    right_child_ids.append(-1)
                    father_ids[current_node_id] = len(tree_nodes) + len(new_nodes) - 1
                    current_node_id += 1
            tree_nodes.extend(new_nodes)
            nodes_to_process = new_nodes
            new_nodes = []
        assert current_node_id == len(tree_nodes) - 1
        # 此时所有的结点都已经计算完毕，存储在tree_nodes中
        father_ids[len(tree_nodes)-1] = -1 # 根节点没有父节点
        return tree_nodes, left_child_ids, right_child_ids, father_ids
    #@profile
    def generate_subset_verification_object(self, subset_idx:List[int]) -> MCTSubsetVerificationObject:
        """MCT支持对于一个集合$S$的子集$s$生成存在性证明。
        subset中保存的是被选中的子集元素的下标。
        
        (1) 使用自底向上的方法确定生成验证对象VO开销最小的方式：

        - 以Merkle哈希树的结构为基础，从subset中出现的每一个元素x开始向上迭代，直至根结点为止。递归的过程中，记录每个节点T的两种证明方式的开销Cost_Tree(T)与Cost_Chain(T)。
        - 对于树节点$T$，
            - 如果$T$是叶子节点，
                - 树证明（类型1）：将当前节点的HASH值加入VO。Cost_Tree(T) = Sizeof(HASH) + Sizeof(LONG)。
                - 链证明（类型2）： 将当前节点和下一结点的HASH值，以及ChainNode的签名加入VO_Chain。Cost_Chain(T) = Sizeof(HASH) * 2 + Sizeof(Signature)。
            - 如果$T$不是叶子节点，T有两个子结点T_left与T_right，T的证明可以使用以下两种方式：
                - 链证明（类型1）：将T_left的链式VO与T_right的链式VO简单的整合在一起即可，Cost_Chain(T) = Cost_Chain(T_left) + Cost_Chain(T_right)。
                - 树证明：生成MerkleTree证明的方式有4种可能方式。
                    - 方式1（类型2）:两个叶子结点都采用Merkle Tree证明。
                    此时可以根据左右孩子的哈希值重构当前结点的哈希值。
                    Cost1(T) = Cost_Tree(T_left) + Cost_Tree(T_right)。
                    - 方式2（类型3）: 左孩子采用Merkle Tree证明，右孩子采用链式证明。
                    左孩子的哈希值可以重放出来，右孩子的哈希值需要加入VO。
                    Cost2(T) = Cost_Tree(T_left) + Sizeof(HASH) + Sizeof(LONG) + Cost_Chain(T_right)。
                    - 方式3（类型4）：左孩子采用链式证明，右孩子采用Merkle Tree证明。
                    右孩子的哈希值可以重放出来，左孩子的哈希值需要加入VO。
                    Cost3(T) = Cost_Tree(T_right) + Sizeof(HASH) + Sizeof(LONG) + Cost_Chain(T_left)。
                    - 方式4（类型5）：两个孩子都采用链式证明。
                    T的哈希值需要加入到VO中。
                    Cost4(T) = Cost_Chain(T_left) + Cost_Chain(T_right) + Sizeof(HASH) + Sizeof(LONG)。
                    - 最终从Cost1-Cost4中选择最小的方式作为Cost_Tree(T)，并记录所选取的方式。
                    
        (2) 根据刚才生成验证对象VO开销最小的方式，从根节点开始自顶向下的构造验证对象VO：

        * VO由VO_Chain和VO_Tree两部分组成，并且在递归调用的过程中全程维护。
            - VO_Chain: [(HASH, HASH_next, ChainNodeSig)]
            - VO_Tree: (Nodes: NodeID:Long-> HASH, RootNodeSignature:HASH, NumLeaf:Long)
        * 对于非叶节点$T$，
            - 如果Cost_Chain(T) < Cost_Tree(T)，则采用全链模式生成VO_Chain。递归左、右子树，并且左右子树均采用Chain模式生成。
            - 如果Cost_Tree(T) < Cost_Chain(T)，
                - 如果是类型2，递归左、右子树采用Tree模式。
                - 如果是类型3，将右孩子节点加入VO_Tree.Nodes。递归左子树采用树模式，右子树采用链模式。
                - 如果是类型4，将左孩子节点加入VO_Tree.Nodes。递归左子树采用链模式，递归右子树采用树模式。
                - 如果是类型5，将T本身加入VO_Tree.Nodes。递归左、右子树均采用链模式。
        * 对于叶节点$T$，
            - 如果采用链模式，将T节点的链式证明加入VO_Chain。
            - 如果采用树模式，将T节点的哈希值加入VO_Tree.Nodes。
        * 当上述递归调用构造完成后，
            - 如果Cost_Tree(T) + Sizeof(Signature) < Cost_Chain(T)，则将Merkle Tree的根节点签名加入VO_Tree.RootNodeSignature，将VO_Tree.NumLeaf设置为集合S的元素数量。
            - 否则将VO_Tree.RootNodeSignature设置为空。
        * VO结构优化：如果VO_Tree.RootNodeSignature为空（即不采用树状验证模式），将VO_Tree从VO中删除。
        """
        for x in subset_idx:
            assert x >= 0 and x < len(self.hash_elements)
        #@profile
        def calculate_min_cost() -> Tuple[Dict[int, Tuple[int,int]], Dict[int, int]]:
            """计算构造VO的最小开销"""
            cost_tree:Dict[int, Tuple[int, int]] = {}
            cost_chain:Dict[int] = {}
            # 将subset中的每个元素转换成对应的树节点ID
            count = 0
            node_ids_to_process = deque()
            for e in subset_idx:
                node_ids_to_process.append(e)
            # 以Merkle哈希树的结构为基础，从叶子节点开始向上迭代，直至根节点为止
            processed_nodes = set()
            while len(node_ids_to_process) > 0:
                node_id = node_ids_to_process.popleft()
                if node_id in processed_nodes:
                    continue
                processed_nodes.add(node_id)
                count += 1
                lc = self.left_child_ids[node_id] # 左孩子ID
                rc = self.right_child_ids[node_id] # 右孩子ID
                if node_id < len(self.hash_elements):
                    # 叶节点
                    # 树证明（类型1）：将当前节点的HASH值加入VO。Cost_Tree(T) = Sizeof(HASH) + Sizeof(LONG)。
                    cost_tree[node_id] = (len(self.tree_nodes[node_id]) + 8,-1)
                    # 链证明（类型2）： 将当前节点和下一结点的HASH值，以及ChainNode的签名加入VO_Chain。Cost_Chain(T) = Sizeof(HASH) * 2 + Sizeof(Signature) + Sizeof(LONG)。
                    full_cost = len(self.tree_nodes[node_id]) * 2 + 32 + 8
                    cost_chain[node_id] = 0
                    if node_id + 1 in subset_idx:
                        cost_chain[node_id] += full_cost / 2
                    if node_id - 1 in subset_idx:
                        cost_chain[node_id] += full_cost / 2
                    if cost_chain[node_id] == 0:
                        cost_chain[node_id] = full_cost
                else:
                    # 非叶节点
                    # 链证明（类型1）：将T_left的链式VO与T_right的链式VO简单的整合在一起即可，Cost_Chain(T) = Cost_Chain(T_left) + Cost_Chain(T_right)。
                    c = 0
                    if lc in cost_chain:
                        c += cost_chain[lc]
                    if rc in cost_chain:
                        c += cost_chain[rc]
                    cost_chain[node_id] = c
                    # 树证明：生成MerkleTree证明的方式有4种可能方式。
                    if rc == -1:
                        # 只有左孩子
                        # 方式1（类型2）:两个叶子结点都采用Merkle Tree证明。
                        c1 = cost_tree[lc][0]
                        # 方式2（类型3）: 左孩子采用Merkle Tree证明，右孩子采用链式证明。
                        c2 = c1
                        # 方式3（类型4）：左孩子采用链式证明，右孩子采用Merkle Tree证明。
                        c3 = cost_chain[lc] + len(self.tree_nodes[node_id]) + 8
                        # 方式4（类型5）：两个孩子都采用链式证明。
                        c4 = c3
                    elif lc in cost_chain and rc in cost_chain:
                        # 两个孩子都已计算过对应的证明开销
                        # 方式1（类型2）:两个叶子结点都采用Merkle Tree证明。
                        # 此时可以根据左右孩子的哈希值重构当前结点的哈希值。
                        # Cost1(T) = Cost_Tree(T_left) + Cost_Tree(T_right)。
                        c1 = cost_tree[lc][0] + cost_tree[rc][0]
                        # 方式2（类型3）: 左孩子采用Merkle Tree证明，右孩子采用链式证明。
                        # 左孩子的哈希值可以重放出来，右孩子的哈希值需要加入VO。
                        # Cost2(T) = Cost_Tree(T_left) + Sizeof(HASH) + Sizeof(LONG) + Cost_Chain(T_right)。
                        c2 = cost_tree[lc][0] + len(self.tree_nodes[rc]) + 8 + cost_chain[rc]
                        # 方式3（类型4）：左孩子采用链式证明，右孩子采用Merkle Tree证明。
                        # 右孩子的哈希值可以重放出来，左孩子的哈希值需要加入VO。
                        # Cost3(T) = Cost_Tree(T_right) + Sizeof(HASH) + Sizeof(LONG) + Cost_Chain(T_left)。
                        c3 = cost_tree[rc][0] + len(self.tree_nodes[lc]) + 8 + cost_chain[lc]
                        # 方式4（类型5）：两个孩子都采用链式证明。
                        # T的哈希值需要加入到VO中。
                        # Cost4(T) = Cost_Chain(T_left) + Cost_Chain(T_right) + Sizeof(HASH) + Sizeof(LONG)。
                        c4 = cost_chain[lc] + cost_chain[rc] + len(self.tree_nodes[node_id]) + 8
                    elif lc in cost_chain and rc not in cost_chain:
                        # 左孩子已经有对应证明开销，右孩子还没有
                        # 方式1（类型2）:两个叶子结点都采用Merkle Tree证明。左孩子重放HASH，右孩子记录HASH
                        c1 = cost_tree[lc][0] + len(self.tree_nodes[rc]) + 8
                        # 方式2（类型3）：左孩子采用Merkle Tree证明，右孩子采用链式证明。
                        c2 = c1
                        # 方式3（类型4）：左孩子采用链式证明，右孩子采用Merkle Tree证明。
                        c3 = len(self.tree_nodes[rc]) + 8 + len(self.tree_nodes[lc]) + 8 + cost_chain[lc]
                        # 方式4（类型5）：两个孩子都采用链式证明。
                        c4 = cost_chain[lc] + 0 + len(self.tree_nodes[node_id]) + 8
                    elif lc not in cost_chain and rc in cost_chain:
                        # 左孩子没有对应证明开销，右孩子有
                        # 方式1（类型2）:两个叶子结点都采用Merkle Tree证明。左孩子重放HASH，右孩子记录HASH
                        c1 = len(self.tree_nodes[node_id]) + 8 + cost_tree[rc][0]
                        # 方式2（类型3）：左孩子采用Merkle Tree证明，右孩子采用链式证明。
                        # Cost2(T) = Cost_Tree(T_left) + Sizeof(HASH) + Sizeof(LONG) + Cost_Chain(T_right)。
                        c2 = len(self.tree_nodes[lc]) + 8 + len(self.tree_nodes[rc]) + 8 + cost_chain[rc]
                        # 方式3（类型4）：左孩子采用链式证明，右孩子采用Merkle Tree证明。
                        # Cost3(T) = Cost_Tree(T_right) + Sizeof(HASH) + Sizeof(LONG) + Cost_Chain(T_left)。
                        c3 = cost_tree[rc][0] + len(self.tree_nodes[lc]) + 8 + 0
                        # 方式4（类型5）：两个孩子都采用链式证明。
                        # Cost4(T) = Cost_Chain(T_left) + Cost_Chain(T_right) + Sizeof(HASH) + Sizeof(LONG)。
                        c4 = 0 + cost_chain[rc] + len(self.tree_nodes[node_id]) + 8
                        # 最终从Cost1-Cost4中选择最小的方式作为Cost_Tree(T)，并记录所选取的方式。
                    else:
                        raise Exception("不应该出现的情况")
                    if c1 == min(c1, c2, c3, c4):
                        cost_tree[node_id] = (c1, 2)
                    elif c2 == min(c1, c2, c3, c4):
                        cost_tree[node_id] = (c2, 3)
                    elif c3 == min(c1, c2, c3, c4):
                        cost_tree[node_id] = (c3, 4)
                    else:
                        cost_tree[node_id] = (c4, 5)  
                #end-of-if
                if self.father_ids[node_id] != -1 and self.father_ids[node_id] not in processed_nodes:
                    node_ids_to_process.append(self.father_ids[node_id])
            #end-of-while
            print(f"  Cost Computation #node processed: {count} from #leafs {len(subset_idx)}")
            return cost_tree, cost_chain
        #@profile
        def construct_vo(cost_tree, cost_chain) -> MCTSubsetVerificationObject:
            """
            根据刚才生成验证对象VO开销最小的方式，从根节点开始自顶向下的构造验证对象VO：

            * VO由VO_Chain和VO_Tree两部分组成，并且在递归调用的过程中全程维护。
                - VO_Chain: [(HASH, HASH_next, ChainNodeSig)]
                - VO_Tree: (Nodes: NodeID:Long-> HASH, RootNodeSignature:HASH, NumLeaf:Long)
            * 对于非叶节点$T$，
                - 如果Cost_Chain(T) <= Cost_Tree(T)，则采用全链模式生成VO_Chain。递归左、右子树，并且左右子树均采用Chain模式生成。
                - 如果Cost_Tree(T) < Cost_Chain(T)，
                    - 如果是类型2，递归左、右子树采用Tree模式。
                    - 如果是类型3，将右孩子节点加入VO_Tree.Nodes。递归左子树采用树模式，右子树采用链模式。
                    - 如果是类型4，将左孩子节点加入VO_Tree.Nodes。递归左子树采用链模式，递归右子树采用树模式。
                    - 如果是类型5，将T本身加入VO_Tree.Nodes。递归左、右子树均采用链模式。
            * 对于叶节点$T$，
                - 如果采用链模式，将T节点的链式证明加入VO_Chain。
                - 如果采用树模式，将T节点的哈希值加入VO_Tree.Nodes。
            * 当上述递归调用构造完成后，
                - 如果Cost_Tree(T) + Sizeof(Signature) < Cost_Chain(T)，则将Merkle Tree的根节点签名加入VO_Tree.RootNodeSignature，将VO_Tree.NumLeaf设置为集合S的元素数量。
                - 否则将VO_Tree.RootNodeSignature设置为空。
            * VO结构优化：如果VO_Tree.RootNodeSignature为空（即不采用树状验证模式），将VO_Tree从VO中删除。对VO_Chain中的Tuple进行去重。
            """
            vo = MCTSubsetVerificationObject(num_element_in_set=len(self.hash_elements))
            def recursive_construct(tree_node_id:int, chain_mode:bool):
                """递归构建VO。chain_mode表示是否用链模式。"""
                if tree_node_id not in cost_tree and tree_node_id not in cost_chain:
                    # 该节点与证明生成无关，可以忽略
                    return
                lc = self.left_child_ids[tree_node_id]
                rc = self.right_child_ids[tree_node_id]
                if tree_node_id >= len(self.hash_elements):
                    # 非叶节点
                    if chain_mode and tree_node_id in cost_chain:
                        # 左右孩子均采用链模式生成
                        recursive_construct(lc, True)
                        if rc != -1:
                            recursive_construct(rc, True)
                    elif cost_chain[tree_node_id] + 8 + 32 <= cost_tree[tree_node_id][0]: 
                        # 左右孩子均采用链模式生成
                        vo.add_tree_node(tree_node_id, self.tree_nodes[tree_node_id])
                        recursive_construct(self.left_child_ids[tree_node_id], True)
                        if rc != -1:
                            recursive_construct(self.right_child_ids[tree_node_id], True)
                    else:
                        # 采用不同的树模式
                        if cost_tree[tree_node_id][1] == 2:
                            # 类型2：左右孩子均采用树模式
                            if lc not in cost_tree:
                                vo.add_tree_node(lc, self.tree_nodes[lc])
                            else:
                                recursive_construct(lc, False)
                            if rc != -1:
                                # 存在右孩子
                                if rc in cost_tree:
                                    recursive_construct(rc, False)
                                else:
                                    vo.add_tree_node(rc, self.tree_nodes[rc])
                        elif cost_tree[tree_node_id][1] == 3:
                            # 方式2（类型3）: 左孩子采用Merkle Tree证明，右孩子采用链式证明。
                            # 左孩子的哈希值可以重放出来，右孩子的哈希值需要加入VO。
                            if lc not in cost_tree:
                                vo.add_tree_node(lc, self.tree_nodes[lc])
                            else:
                                recursive_construct(lc, False)
                            if rc != -1:
                                vo.add_tree_node(rc, self.tree_nodes[rc])
                                if rc in cost_chain:
                                    recursive_construct(rc, True)
                        elif cost_tree[tree_node_id][1] == 4:
                            # 方式3（类型4）：左孩子采用链式证明，右孩子采用Merkle Tree证明。
                            # 右孩子的哈希值可以重放出来，左孩子的哈希值需要加入VO。
                            vo.add_tree_node(lc, self.tree_nodes[lc])
                            if lc in cost_chain:
                                recursive_construct(lc, True)
                            if rc != -1:
                                if rc not in cost_tree:
                                    vo.add_tree_node(rc, self.tree_nodes[rc])
                                else:
                                    recursive_construct(rc, False)
                        elif cost_tree[tree_node_id][1] == 5:
                            #- 方式4（类型5）：两个孩子都采用链式证明。
                            # T的哈希值需要加入到VO中。
                            vo.add_tree_node(tree_node_id, self.tree_nodes[tree_node_id])
                            if lc in cost_chain:
                                recursive_construct(lc, True)
                            if rc != -1 and rc in cost_chain:
                                recursive_construct(rc, True)
                else:
                    # 叶节点
                    """
                    - 如果采用链模式，将T节点的链式证明加入VO_Chain。
                    - 如果采用树模式，将T节点的哈希值加入VO_Tree.Nodes。
                    """
                    if chain_mode:
                        # 采用链模式
                        if tree_node_id < len(self.hash_elements) - 1:
                            vo.add_chain_node(self.tree_nodes[tree_node_id], self.tree_nodes[tree_node_id + 1], self.chain_nodes[tree_node_id], tree_node_id)
                        else:
                            vo.add_chain_node(self.tree_nodes[tree_node_id-1], self.tree_nodes[tree_node_id], self.chain_nodes[tree_node_id-1], tree_node_id-1)
                    else:
                        # 采用树模式
                        vo.add_tree_node(tree_node_id, self.tree_nodes[tree_node_id])
            root_node_id = len(self.tree_nodes) - 1 # 从根节点开始
            if cost_chain[root_node_id] < cost_tree[root_node_id][0] + 32:
                # 采用全链模式
                recursive_construct(root_node_id, True)
                vo.tree_root_signature = None
                vo.tree = {}
            else:
                # 采用树模式
                vo.tree_root_signature = self.tree_signature
                vo.tree_num_leaf = len(self.hash_elements)
                recursive_construct(root_node_id, False)
            # 优化vo结构，消除链证明中无用的区间
            vo.chain = sorted(vo.chain, key=lambda x:x[0])
            used_chain_proof = {}
            for i in range(len(vo.chain)):
                t = vo.chain[i]
                element, next_element, sig, idx = t
                if idx in subset_idx and idx not in used_chain_proof:
                    used_chain_proof[idx] = i
                if idx + 1 in subset_idx and idx + 1 not in used_chain_proof:
                    used_chain_proof[idx+1] = i
            opt_vo_chain = [vo.chain[idx] for idx in set(used_chain_proof.values())]
            vo.chain = opt_vo_chain
            vo.chain.sort(key=lambda x: x[0])
            return vo
        cost_tree, cost_chain = calculate_min_cost()
        vo = construct_vo(cost_tree, cost_chain)
        if vo.tree_root_signature is None:
            replayed_element_set = set()
            for i in vo.chain:
               replayed_element_set.add(i[0])
               replayed_element_set.add(i[1])
            assert len(subset_idx) <= len(replayed_element_set)
        return vo
    
def generate_set_intersection_ads(dataset:Dict[bytes, List[bytes]], pk:bytes, prefix_lens:List[int]) -> Dict[int, Dict[bytes, MerkleChainTree]]:
    """生成集合数据集的ADS"""
    """对于数据集中关键词为keyword的集合$S$，利用$pk || keyword || |S|$作为验证签名密钥sk，生成该集合的MCT。
"""
    ads = {}
    for prefix_len in prefix_lens:
        print(f"正在处理前缀长度:{prefix_len}")
        ads[prefix_len] = {}
        for key in dataset.keys():
            s = dataset[key]
            s.sort()
            hash_s = [LEFT_BOUND] + [sha256(bytes(e)).digest() for e in s] + [RIGHT_BOUND]
            hash_s.sort()
            sk = pk + b'|' + bytes(key) + b'|' + len(hash_s).to_bytes(8, 'big')
            #print(f"sk={sk}")
            mct = MerkleChainTree(hash_s, sk, prefix_len)
            ads[prefix_len][key] = mct
    return ads
    
import math
import mmh3
from bitarray import bitarray

class BloomFilterADS:
    
    def __init__(self, n:int, positive_rate:float, left_bound:bytes, right_bound:bytes, sk:bytes, subset:List[bytes]):
        size, hash_count = self.calculate_size(n, positive_rate)
        self.size = size
        self.hash_count = hash_count
        self.bit_array = bitarray(size)
        self.bit_array.setall(0)
        self.generate_signature(sk, subset)

    def generate_signature(self, sk:bytes, subset:List[bytes]):
        """
        生成Bloom Filter的签名。
        :param subset: 要插入的元素列表
        :return: Bloom Filter的签名
        """
        for item in subset:
            self.add(item)
        raw_bytes = self.bit_array.tobytes()
        # 对raw_bytes进行hmac签名
        self.signature = hmac.new(sk, raw_bytes, sha256).digest()

    def add(self, item:bytes):
        for seed in range(self.hash_count):
            #print(item)
            result = mmh3.hash(item, seed) % self.size
            self.bit_array[result] = 1

    def __contains__(self, item:bytes):
        for seed in range(self.hash_count):
            result = mmh3.hash(item, seed) % self.size
            if self.bit_array[result] == 0:
                return False
        return True

    def calculate_size(self, n, p):
        """
        计算Bloom Filter的大小和哈希函数的数量。

        :param n: 预期插入的元素数量
        :param p: 期望的误报率
        :return: Bloom Filter的大小和哈希函数的数量
        """
        m = - (n * math.log(p)) / (math.log(2) ** 2)
        k = (m / n) * math.log(2)
        return int(m), int(k)
    
    def vo_size(self) -> int:
        size = 0
        size = size + 16 + 32 + len(self.bit_array.tobytes()) + 8
        return size

class PartitionADS:
    """一个集合分区的ADS"""
    def __init__(self):
        self.mct:Dict[int, MerkleChainTree] = {} # 不同前缀长度的MCT ADS
        self.bf:Dict[int, BloomFilterADS] = {} # 不同前缀长度的BF ADS
        self.left_bound:bytes = None
        self.right_bound:bytes = None
        self.idx = -1
    def vo_size(self):
        size = 0
        size += 8
        for l in self.mct.keys():
            size += self.mct[l].vo_size() + 8
        size += 8
        for l in self.bf.keys():
            size += self.bf[l].vo_size() + 8
        size += 2 * 32
        return size
    
def construct_ads_for_set(keyword: bytes, set:List[bytes], pk:bytes, prefix_lens:List[int]) -> List[PartitionADS]:
    """为某个集合构建分区ADS"""
    
    pass    

# %% 测试generate_partitioned_ads
#dataset = {bytes(1): [1,2,3,4,5,6, 7,8, 9, 10,11]}
#ads = generate_partitioned_ads(dataset, b'1'*32, [4, 32], 3)
#x=10
# %%
    
class SetIntersectionVerificationObject:
    """集合交集计算验证对象"""
    def __init__(self):
        self.s_size:int = -1
        self.r_size:int = -1
        self.r_mct:Dict[int, MCTSubsetVerificationObject] = {}
        self.s_mct:Dict[int, MCTSubsetVerificationObject] = {}
        
    def vo_size(self):
        # s_size, r_size
        size = 16
        for l in self.r_mct.keys():
            mvo_size = self.r_mct[l].vo_size()
            print(f"level={l}, vo_r_size={mvo_size}")
            size += mvo_size + 1
        for l in self.s_mct.keys():
            svo_size = self.s_mct[l].vo_size()
            print(f"level={l}, vo_s_size={svo_size}")
            size += svo_size + 1
        return size
def generate_set_intersection_verification_object(ads:Dict[int, Dict[bytes, MerkleChainTree]], prefix_lens:List[int], r_index:bytes, s_index:bytes) -> Tuple[Set[bytes], SetIntersectionVerificationObject]:
    """服务器端：给定查询集合$R$和$S$，生成VO。"""
    full_ads_r = ads[32][r_index]
    assert full_ads_r != None
    full_ads_s = ads[32][s_index]
    assert full_ads_s != None
    set_r = full_ads_r.hash_elements
    set_s = full_ads_s.hash_elements
    assert(len(set_r) <= len(set_s))
    # 计算$R \cap S$，计算的过程中记录$R$中每个元素$x$需要与对应$S$元素区分所需的最小哈希前缀长度$L(x)$。
    result = set(set_r).intersection(set(set_s))
    vo = SetIntersectionVerificationObject()
    def find_element_interval(s:List[bytes], x:bytes) -> int:
        from bisect import bisect_right
        i = bisect_right(s, x)
        return i-1
    def calculate_min_prefix_len(s:List[bytes], x:bytes, prefix_lens:List[int]) -> int:
        from bisect import bisect_right
        i = bisect_right(s, x)
        assert i >= 1
        p = prefix_lens[0]
        for l in prefix_lens:
            if x[0:l] != s[i-1][0:l] and x[0:l] != s[i][0:l]: # 比较x与s[i-1]、s[i]的前缀，如果相等，则返回当前前缀长度。
                p = l
                break
        return p
    r_lens = [calculate_min_prefix_len(set_s, x, prefix_lens) for x in set_r]
    for i in range(len(r_lens)):
        if set_r[i] in result:
            r_lens[i] = 32
    print(f"计算前缀情况：最小前缀长度为：{min(r_lens)}，最大前缀长度为{max(r_lens)}")
    # 将$|R|$和$|S|$的信息放入VO.RSize和VO.SSize。
    vo.r_size = len(set_r)
    vo.s_size = len(set_s)
    # 对于每一个哈希前缀长度$l$
    for l in prefix_lens:
        print(f"正在处理前缀长度:{l}")
        if r_lens.count(l) == 0:
            print(f"前缀长度{l}未使用，跳过")
            continue
        # 提取$R$子集$r_l = \{x|x \in R, L(x) = l\}$。
        r_l = [x for x in range(0, len(r_lens)) if r_lens[x] == l]
        r_mct = ads[l][r_index].generate_subset_verification_object(r_l)
        vo.r_mct[l] = r_mct
        s_l = set()
        for x in r_l:
            if set_r[x] == LEFT_BOUND[0:l]:
                s_l.add(0)
                s_l.add(1)
                continue
            if set_r[x] == RIGHT_BOUND[0:l]:
                s_l.add(vo.s_size-1)
                s_l.add(vo.s_size-2)
                continue
            s_idx = find_element_interval(set_s, set_r[x])
            if set_s[s_idx] == set_r[x]:
                s_l.add(s_idx)
            else:
                s_l.add(s_idx)
                s_l.add(s_idx+1)
        s_l = sorted(list(s_l))
        s_mct = ads[l][s_index].generate_subset_verification_object(s_l)
        vo.s_mct[l] = s_mct
    # 将交集计算结果以及$VO$返回用户。
    return result, vo

def verify_set_intersection_vo(result:List[bytes], r_keywords:bytes, s_keywords:bytes,
                               pk:bytes, vo:SetIntersectionVerificationObject) -> Tuple[bool, str]:
    """客户端验证集合交集计算验证对象"""
    # 验证$R$的完整性。
    def verify_vo_of_r():
        # 对于每一个哈希前缀长度$l$，根据私钥$pk$、R的关键词keyword，以及VO.RSize，校验VO.R[l]的签名。任一签名校验失败，则完整性验证失败。
        replayed_r = set()
        for l in vo.r_mct.keys():
            print(f"验证R集合VO前缀{l}.")
            r_mct = vo.r_mct[l]
            sk = pk + b'|' + bytes(r_keywords) + b'|' + vo.r_size.to_bytes(8, 'big')
            #print(f"sk={sk}")
            flag, r_l, _ = r_mct.verify(sk, [])
            if not flag:
                print(f"R集合前缀{l}验证失败.")
                return False, f"R集合前缀{l}验证失败.", None
            replayed_r.update(r_l)
        # 从所有的VO.R[l]中提取R的子集$r_l$，计算$R' = \cup {r_l}$。验证|R'| = VO.RSize是否成立，如果不成立，验证失败。
        # 合并replayed_r中出现的元素（消除所有的低前缀长度子串）
        tmp_l = list(replayed_r)
        tmp_l.sort()
        for i in range(len(tmp_l) - 1):
            l = len(tmp_l[i])
            if tmp_l[i][0:l] == tmp_l[i+1][0:l]:
                replayed_r.remove(tmp_l[i])
        if len(replayed_r) != vo.r_size:
            print(f"R集合长度验证失败, 预期长度{vo.r_size}，实际获得长度{len(replayed_r)}")
            return False, f"R集合长度验证失败.", None
        return True, "", replayed_r
    def verify_vo_of_s():
        # 验证$S$的完整性
        # 对于每一个哈希前缀长度$l$，根据私钥$pk$、S的关键词keyword，以及VO.SSize，校验VO.S[l]的签名。任意签名校验失败则完整性验证失败。
        replayed_s_intervals = set()
        for l in vo.s_mct:
            print(f"验证S集合VO前缀{l}.")
            s_mct = vo.s_mct[l]
            sk = pk + b'|' + bytes(s_keywords) + b'|' + vo.s_size.to_bytes(8, 'big')
            flag, s_l, _ = s_mct.verify(sk, [])
            if not flag:
                print(f"S集合前缀{l}验证失败.")
                return False, f"S集合前缀{l}验证失败.", None
            # 从所有的VO.S[l]中提取连续的子集区间$S'$。
            # 对于VO.S[l].VO_Chain中的每一组Tuple，将$(S[i], S[i+1])$加入到$S'$中。
            known_leafs = {}
            for tuple in s_mct.chain:
                known_leafs[tuple[3]] = tuple[0]
                known_leafs[tuple[3]+1] = tuple[1]
            # 对于VO.S[l].VO_Tree中出现的S[i]与S[i+1]连续元素，将两者添加到$S'$中。
            for node_id in s_mct.tree:
                if node_id >= vo.s_size:
                    continue # 跳过非叶节点
                known_leafs[node_id] = s_mct.tree[node_id]
            for node_id in known_leafs.keys():
                if node_id + 1 in known_leafs:
                    replayed_s_intervals.add((known_leafs[node_id], known_leafs[node_id+1]))
                if node_id + 1 == vo.s_size - 1:
                    replayed_s_intervals.add((known_leafs[node_id], RIGHT_BOUND[0:l]))
        return True, msg, replayed_s_intervals
    def verify_intersection(result, replayed_r, replayed_s_intervals):
        """验证R intersect S的完备性"""
        # 对于$R'$中的每一个元素$x$，
        # 如果$x$能在$S'$中的Tuple区间中出现，则$x$应该在$R intersect S$中。如果没有出现，则完备性验证失败。
        # 如果$S'$中存在$S[i] < x < S[i+1]$的区间，$x$不应出现在$R intersect S$中。如果出现，则完备性验证失败。
        for x in replayed_r:
            s_tuple = None
            for t in replayed_s_intervals:
                if t[0] <= x and x <= t[1]:
                    if s_tuple is None:
                        s_tuple = t
                    elif len(t[0]) > len(s_tuple[0]):
                        s_tuple = t
            if s_tuple == None:
                print(f"元素{x}未在S集合中找出覆盖区间.")
                return False, f"元素{x}未在S集合中找出覆盖区间."
            if s_tuple[0] == x or x == s_tuple[1]:
                if x not in result:
                    print(f"元素{x}应该在交集中出现，但未出现在计算结果中.")
                    return False, f"元素{x}应该在交集中出现，但未出现在计算结果中."
            else:
                if x in result:
                    print(f"元素{x}不应该在交集中出现，但出现在计算结果中.")
                    return False, f"元素{x}不应该在交集中出现，但出现在计算结果中."
        return True, "验证通过"
            
    flag, msg, replayed_r_set = verify_vo_of_r()
    if not flag:
        return flag, msg
    flag, msg, replayed_s_intervals = verify_vo_of_s()
    if not flag:
        return flag, msg
    flag, msg = verify_intersection(result, replayed_r_set, replayed_s_intervals)
    return flag, msg

########### 测试代码部分 ###########

if False: # 子集验证的代码
    # 生成长度为10和20的随机整数集合R和S
    import random
    #random.seed(42)
    # 生成长度为10的随机整数集合R
    R = set(random.sample(range(1, 10000), 10))
    hashR = [LEFT_BOUND] + [sha256(bytes(e)).digest() for e in R] + [RIGHT_BOUND]
    hashR.sort()
    # 生成长度为20的随机整数集合S
    S = set(random.sample(range(1, 10000), 20))
    hashS = [LEFT_BOUND] + [sha256(bytes(e)).digest() for e in S] + [RIGHT_BOUND]
    hashS.sort()
    # 生成长度为20的随机整数集合S
    #print("集合R:", R, hashR)
    #print("集合S:", S, hashS)
    big_R = set(random.sample(range(1, 10000), 1000))
    hash_bigR = [LEFT_BOUND] + [sha256(bytes(e)).digest() for e in big_R] + [RIGHT_BOUND]
    hash_bigR.sort()

    # 测试Merkle Chain Tree结构生成
    sk = b'\x01' * 32
    treeR4 = MerkleChainTree(hashR, sk, 32)
    treeS4 = MerkleChainTree(hashS, sk, 32)

    # 测试子集验证对象生成功能
    #voR4 = treeR4.generate_subset_verification_object([1,3,5])
    #voS4 = treeS4.generate_subset_verification_object([2,4,6,8,10,12,14,16,18,20])
    #ss = set(random.sample(range(len(hash_bigR) + 3), 60))
    #voBigR = treeBigR.generate_subset_verification_object(random.sample(range(len(hash_bigR) + 3), 10))

    # 测试子集验证对象校验功能
    #flag, subset, set_ranges = voBigR.verify(sk)
    #print(flag)
    #print(flag, subset, set_ranges)
    #print(flag, ss.intersection(subset), set_ranges)

    # 循环自动测试
    PREFIX_LEN = 4
    treeBigR = MerkleChainTree(hash_bigR, sk, PREFIX_LEN)
    for slen in range(1, len(big_R)):
        for i in range(100):
            pick_index = random.sample(range(len(hash_bigR)), slen)
            pickset = set([hash_bigR[x][0:PREFIX_LEN] for x in pick_index])
            voBigR = treeBigR.generate_subset_verification_object(pick_index)
            flag, subset, set_ranges = voBigR.verify(sk, pickset)
            assert flag and len(pickset.intersection(subset)) == len(pickset)
            import copy
            modifiedVO = copy.deepcopy(voBigR)
            if len(voBigR.tree) > 0:
                # 从modifiedVO.tree中随机选取一个元素删除
                delete_key = random.choice(list(voBigR.tree.keys()))
                modifiedVO.tree.pop(delete_key)
            if len(voBigR.chain) > 0:
                # 从modifiedVO.chain中随机选取一个元素删除
                delete_key = random.choice(range(len(voBigR.chain)))
                modifiedVO.chain.pop(delete_key)
            flag, subset, set_ranges = modifiedVO.verify(sk, pickset)
            if len(pickset.intersection(subset)) != len(pickset):
                print("结果被篡改，正在校验是否能检测出")
                assert flag == False

if False:
    s = [482, 451, 456, 714, 554, 779, 653, 495, 497, 83, 56, 123, 732]
    sub_idx = [1, 2, 4, 5, 7, 8]
    hash_s = [LEFT_BOUND] + [sha256(bytes(e)).digest() for e in s] + [RIGHT_BOUND]
    hash_s.sort()
    mct = MerkleChainTree(hash_s, b'1'*32, 32)
    vo = mct.generate_subset_verification_object(sub_idx)
    print(vo)

if False:
    # 测试MCT的生成和验证功能
    import random
    keys = [1, 2, 3]
    sets = {bytes(1): [768, 649, 137, 907, 15, 916, 789, 277, 24, 921, 26, 157, 933, 808, 426, 428, 45, 692, 567, 441, 826, 960, 706, 836, 709, 580, 456, 210, 217, 860, 608, 483, 612, 997, 886, 762, 763, 892, 382, 383], 
            bytes(2): [768, 384, 386, 6, 264, 779, 528, 532, 281, 154, 30, 927, 928, 929, 39, 427, 689, 947, 308, 445, 701, 62, 833, 579, 453, 197, 715, 846, 336, 211, 856, 601, 220, 488, 106, 110, 116, 117, 759, 764, 510]}
    prefix_lens = [4, 32]
    pk = b'\x01' * 32
    ads = generate_set_intersection_ads(sets, pk, prefix_lens)
    print("ADS已建立")
    result, vo = generate_set_intersection_verification_object(ads, prefix_lens, bytes(1), bytes(2))
    print(result)
    flag, message = verify_set_intersection_vo(result, bytes(1), bytes(2), pk, vo)
    print(flag)

if False:
    # 随机测试MCT的生成和验证功能
    # 随机生成两个长度在100~1000之间的集合s1和s2
    import random
    for i in range(2000):
        s1 = set(random.sample(range(1, 10000), random.randint(5, 1000)))
        s2 = set(random.sample(range(1, 10000), random.randint(5, 1000)))
        # 交换s1和s2如果s1的规模较大
        if len(s1) > len(s2):
            s1, s2 = s2, s1
        # 生成ADS
        sets = {bytes(1): list(s1), bytes(2): list(s2)}
        prefix_lens = [4, 32]
        pk = b'\x01' * 32
        ads = generate_set_intersection_ads(sets, pk, prefix_lens)
        print(f"ADS已建立, |R| = {len(s1)} & |S| = {len(s2)}")
        result, vo = generate_set_intersection_verification_object(ads, prefix_lens, bytes(1), bytes(2))
        flag, message = verify_set_intersection_vo(result, bytes(1), bytes(2), pk, vo)
        assert flag == True
        print("验证通过")
        if len(result) > 2:
            modified_result = sorted(list(result))
            # 从modified_result中随机选择一个元素删除
            random_element = random.choice(modified_result)
            modified_result.remove(random_element)
            flag, message = verify_set_intersection_vo(modified_result, bytes(1), bytes(2), pk, vo)
            print("数据已篡改，正在检测篡改是否能被验证")
            assert flag == False
            
if False:
    import random
    keys = [1, 2, 3]
    sets = {bytes(1): random.sample(range(1, 5000000), 100), 
            bytes(2): random.sample(range(1, 5000000), 1000)}
    prefix_lens = [4, 32]
    pk = b'\x01' * 32
    ads = generate_set_intersection_ads(sets, pk, prefix_lens)
    print("ADS已建立")
    result, vo = generate_set_intersection_verification_object(ads, prefix_lens, bytes(1), bytes(2))
    print(result)
    flag, message = verify_set_intersection_vo(result, bytes(1), bytes(2), pk, vo)
    print("VO Size:", vo.vo_size())
    
# %%

def debug_bf():
    import random
    keys = [1, 2, 3]
    sets = {bytes(1): random.sample(range(1, 5000000), 100), 
            bytes(2): random.sample(range(1, 5000000), 1000)}
    pk = b'\x01' * 32
    # 生成BF版本的ADS
    s = random.sample(range(1, 5000000), 1000)
    hash_s = [LEFT_BOUND] + [sha256(bytes(e)).digest() for e in s] + [RIGHT_BOUND]
    hash_s.sort()
    prefix_s = [x[0:4] for x in hash_s]
    bf = BloomFilterADS(2048, 0.1, LEFT_BOUND, RIGHT_BOUND, pk, prefix_s)
    print(bf.hash_count, bf.size)
    print(bf.vo_size())  
#debug_bf()

def debug_bf_based_ads():
    import random
    keys = [1, 2, 3]
    sets = {bytes(1): random.sample(range(1, 5000000), 100), 
            bytes(2): random.sample(range(1, 5000000), 1000)}
    pk = b'\x01' * 32
    # 生成BF版本的ADS
    r = random.sample(range(1, 5000000), 100)
    s = random.sample(range(1, 5000000), 1000)
    hash_r = [LEFT_BOUND] + [sha256(bytes(e)).digest() for e in r] + [RIGHT_BOUND]
    hash_r.sort()
    prefix_r = [x[0:4] for x in hash_r]
    hash_s = [LEFT_BOUND] + [sha256(bytes(e)).digest() for e in s] + [RIGHT_BOUND]
    hash_s.sort()
    prefix_s = [x[0:4] for x in hash_s]
    mct = MerkleChainTree(hash_s, pk, 4)
    bf = BloomFilterADS(1000, 0.1, LEFT_BOUND, RIGHT_BOUND, pk, prefix_s)
    print(bf.hash_count, bf.size, bf.vo_size())
    related_idx = set()
    def get_position(x:bytes, s:List[bytes]):
        for i in range(len(s) - 1):
            if s[i] == x :
                return set([i])
            elif s[i] < x and x < s[i + 1]:
                return set([i, i+1])
        return None
    for x in prefix_r[1:-1]:
        if x in bf:
            related_idx.update(get_position(x, prefix_s))
    related_idx = sorted(list(related_idx))
    print(related_idx)
    mct_vo = mct.generate_subset_verification_object(related_idx)
    print(mct_vo.vo_size())
#debug_bf_based_ads()

#@profile
def generate_bf_based_vo_for_s(r:List[bytes], s:List[bytes], prefix_len:int, bf:BloomFilterADS, mct:MerkleChainTree):
    """生成基于Bloom Filter的验证对象"""
    prefix_r = [x[0:prefix_len] for x in r]
    related_idx = set()
    for x in prefix_r:
        if not x in bf:
            continue
        #print(f"Process {x}")
        idx = bisect_right(s, x) # 在s中定位x
        if idx >= 1 and s[idx-1][0:prefix_len] == x:
            related_idx.add(idx-1)
        else:
            if idx-1 >= 0:
                related_idx.add(idx-1)
            if idx <= len(s):
                related_idx.add(idx)
    related_idx = sorted([x+1 for x in related_idx]) # 因为MCT中包含LEFT_BOUND,因此所有集合下标需要+1
    if len(related_idx) > 0:
        mct_vo = mct.generate_subset_verification_object(related_idx)
    else:
        mct_vo = None
    return bf, mct_vo

def generate_partition_ads(dataset:Dict[bytes, List[bytes]], pk:bytes, prefix_lens:List[int], seg_size:int, false_positive_rate:float) \
    -> Dict[bytes, List[PartitionADS]]: # {keyword: [PartitionADS]}
    """
1. 对于一个集合S，计算分区数 P = |S|/SegSize （向上取整）。
2. 将S依次划分为P个区间，每个区间是一个左闭右开区间。
3. 为每一个区间构建MCT树, 签名密钥是 sk || 左边界 || 右边界了, MCT树记录左右边界信息.
4. 为每一个区间构建Bloom Filter, 存储该区间内出现的所有集合元素; 为Bloom Filter生成签名, 签名密钥是 sk || 左边界 || 右边界.
    """
    ads = {}
    for keyword in dataset.keys():
        print(f"正在为关键词{keyword}生成ADS")
        s = dataset[keyword]
        hash_s = s
        # 将s按照seg_size分隔成若干个区间
        hash_s.sort()
        pivots = list(range(0, len(hash_s), seg_size))
        s_ads = []
        for i in range(len(pivots)): # 构造每一个区间的ADS
            if i == 0:
                left = LEFT_BOUND
            else:
                left = hash_s[pivots[i]]
            if i < len(pivots) - 1: # 非最后一个区间
                right = hash_s[pivots[i+1]]
                s_part = hash_s[pivots[i]:pivots[i+1]] # 该区间的元素
            else:
                right = RIGHT_BOUND
                s_part = hash_s[pivots[i]:] # 该区间的元素
            print(f"  正在处理分区: ", i, left, right)
            # 为区间s_part集合构建MCT验证数据结构
            sk = pk + bytes(keyword) + b'|' + len(s_part).to_bytes(8, 'big') + b'|' + left + b'|' + right + i.to_bytes(8, 'big')
            mct = {}
            for l in prefix_lens:
                mct[l] = MerkleChainTree([LEFT_BOUND] + s_part + [RIGHT_BOUND], sk, l)
            # 为区间s_part集合构建BF验证数据结构
            bf = {}
            for l in prefix_lens:
                bf[l] = BloomFilterADS(min(seg_size, len(s_part)), false_positive_rate, left, right, sk, [x[0:l] for x in s_part])
            ads_part = PartitionADS()
            ads_part.left_bound = left
            ads_part.right_bound = right
            ads_part.bf = bf
            ads_part.mct = mct
            ads_part.idx = i
            s_ads.append(ads_part)
        ads[keyword] = s_ads
    return ads

class PartitionIntersectionVO:
    def __init__(self):
        self.seg_size = None
        self.left = None
        self.right = None
        self.idx = -1
        self.mct_vo:Dict[int, MCTSubsetVerificationObject] = {}
        self.bf_vo:Dict[int, BloomFilterADS] = {}
    def vo_size(self):
        size = 8 + 32 * 2 + 8
        for l in self.mct_vo.keys():
            if self.mct_vo[l] is not None:
                size += self.mct_vo[l].vo_size() + 8
        size += 8
        for l in self.bf_vo.keys():
            if self.bf_vo[l] is not None:
                size += self.bf_vo[l].vo_size() + 8
        return size

def calculate_min_prefix_len(s:List[bytes], x:bytes, prefix_lens:List[int]) -> int:
    """计算为了在集合s中区分元素x所需要的最小长度前缀"""
    from bisect import bisect_right
    i = bisect_right(s, x)
    p = prefix_lens[-1]
    for l in prefix_lens:
        if i >= 0 and i < len(s) and x[0:l] == s[i][0:l]:
            continue
        if i-1 >= 0 and i-1 < len(s) and x[0:l] == s[i-1][0:l]:
            continue
        # 比较x与s[i-1]、s[i]的前缀，如果与两侧均不等，则返回当前前缀长度。
        p = l
        break
    return p

def generate_partition_intersection_vo_r_part(r_ads:List[PartitionADS], r:List[bytes], s:List[bytes], prefix_lens:List[int]) -> List[PartitionIntersectionVO]:
    print("正在为R生成存在性证明..")
    # 对于R的每一个分区R_i, 提取S中对应分区的子集S_i, 为R_i中的每一个元素x计算所需的最小前缀长度L(x), 根据L(x)为R中该分区的所有元素生成存在性证明VO.R[i].
    r_vo = []
    for part in r_ads:
        print(f"  正在处理分区 {part.idx}", part.left_bound, part.right_bound)
        mct = part.mct
        # 分区集合
        r_part = [x for x in r if x >= part.left_bound and x < part.right_bound]
        # 提取S中对应分区子集s_part
        if part.left_bound == LEFT_BOUND and part.right_bound == RIGHT_BOUND:
            s_part = s
        else:
            s_part = [x for x in s if x >= part.left_bound and x < part.right_bound]
        # 计算R_i中每一个元素的最小前缀长度
        r_lens = [calculate_min_prefix_len(s_part, x, prefix_lens) for x in r_part]
        result = set(r_part).intersection(s_part)
        for i in range(len(r_part)): # 出现在交集中的元素前缀长度必须为32
            if r_part[i] in result:
                r_lens[i] = 32
        print(f"    计算前缀情况：最小前缀长度为：{min(r_lens)}，最大前缀长度为{max(r_lens)}")
        print(f"    r_part_size = {len(r_part)}")
        # 为R_i中的每一个元素x生成存在性证明VO.R[i].
        r_part_vo = PartitionIntersectionVO()
        r_part_vo.left = part.left_bound
        r_part_vo.right = part.right_bound
        r_part_vo.seg_size = len(r_part)
        r_part_vo.idx = part.idx
        # 基于MCT生成存在性证明
        for l in prefix_lens:
            print(f"    正在处理前缀长度:{l}")
            if r_lens.count(l) == 0:
                print(f"    前缀长度{l}未使用，跳过")
                continue
            r_l = [x + 1 for x in range(0, len(r_lens)) if r_lens[x] == l]
            # 因为构建ADS时自动加入了LEFT_BOUND和RIGHT_BOUND, 因此需要在r_l中每个元素加1
            r_mct_vo = part.mct[l].generate_subset_verification_object(r_l)
            r_part_vo.mct_vo[l] = r_mct_vo
            print(f"    VO规模: {r_mct_vo.vo_size()}")
        r_vo.append(r_part_vo)
    return r_vo

#@profile
def generate_partition_intersection_vo_s_part(s_ads:List[PartitionADS], r:List[bytes], s:List[bytes], prefix_lens:List[int]) -> List[PartitionIntersectionVO]:
    print("正在为S生成存在性证明..")
    """
    对于S的每一个分区S_i, 提取R中对应分区的子集R_i, 按以下两个模式生成验证对象:
        + 基于MCT的方式为R_i和S_i交集生成S_i的验证对象vo_mct.
        + 基于Bloom Filter的方式为R_i和S_i的交集生成验证对象vo_bf.
            * 将bf内容以及bf的签名加入vo_bf.
            * 根据R_i中所有bf汇报为阳性的元素构成子集,为该子集生成mct验证对象.
        + 比较vo_mct和vo_bf的大小, 选择较小的一个作为VO.S[i] 
    """
    s_vo = []
    for part in s_ads:
        print(f"  正在处理分区{part.idx}", part.left_bound, part.right_bound)
        # 分区集合
        if part.left_bound == LEFT_BOUND and part.right_bound == RIGHT_BOUND:
            s_part = s 
            r_part = r
        else:
            s_part = [x for x in s if x >= part.left_bound and x < part.right_bound]
            # 提取R中对应分区子集r_part
            r_part = [x for x in r if x >= part.left_bound and x < part.right_bound]
        if len(r_part) == 0:
            print(f"    对应R分区不包含有效元素,跳过")
            continue
        # 计算R_i中每一个元素的最小前缀长度
        r_lens = [calculate_min_prefix_len(s_part, x, prefix_lens) for x in r_part]
        s_part_vo = PartitionIntersectionVO()
        s_part_vo.seg_size = len(s_part)
        s_part_vo.idx = part.idx
        s_part_vo.left = part.left_bound
        s_part_vo.right = part.right_bound
        for l in prefix_lens:
            print(f"    正在处理前缀长度:{l}")
            if r_lens.count(l) == 0:
                print(f"    前缀长度{l}未使用，跳过")
                continue
            r_l = [x for x in range(0, len(r_lens)) if r_lens[x] == l]
            print(f"    前缀子集长度:{len(r_l)}")
            s_l = set()
            for x in r_l:
                e = r_part[x]
                s_idx = bisect_right(s_part, e) - 1
                if s_part[s_idx] == e:
                    s_l.add(s_idx)
                else:
                    s_l.add(s_idx)
                    s_l.add(s_idx+1)
            s_l = sorted([x+1 for x in s_l])
            # 因为在构建ADS时自动加入了LEFT_BOUND和RIGHT_BOUND, 因此需要在s_l中每个元素加1
            # 生成MCT版本的VO
            s_mct_vo = part.mct[l].generate_subset_verification_object(s_l)
            cost_mct_vo = s_mct_vo.vo_size()
            # 生成BF版本的VO
            s_bf_vo = generate_bf_based_vo_for_s(r_part, s_part, l, part.bf[l], part.mct[l])
            cost_bf_vo = s_bf_vo[0].vo_size()
            if s_bf_vo[1] is not None:
                cost_bf_vo += s_bf_vo[1].vo_size()
            print(f"    Cost MCT: {cost_mct_vo}, Cost VO: {cost_bf_vo} ({s_bf_vo[0].vo_size()})")
            if cost_mct_vo <= cost_bf_vo:
                s_part_vo.mct_vo[l] = s_mct_vo
            else:
                s_part_vo.bf_vo[l] = s_bf_vo[0]
                s_part_vo.mct_vo[l] = s_bf_vo[1]
        s_vo.append(s_part_vo)
    return s_vo
        

#@profile
def generate_partition_intersection_vo(dataset:Dict[bytes, List[bytes]], ads:Dict[bytes, List[PartitionADS]], r_key:bytes, s_key:bytes, prefix_lens:List[int]) -> Tuple[List[PartitionIntersectionVO], List[PartitionIntersectionVO]]:
    r = dataset[r_key]
    s = dataset[s_key]
    r_ads = ads[r_key]
    s_ads = ads[s_key]
    s_vo = []
    # 生成R的存在性证明
    r_vo = generate_partition_intersection_vo_r_part(r_ads, r, s, prefix_lens)
    #print(r_vo)
    # 生成S的存在性证明
    s_vo = generate_partition_intersection_vo_s_part(s_ads, r, s, prefix_lens)
    #print(s_vo)
    return r_vo, s_vo

class MultiKeywordVerificationObject:
    def __init__(self):
        self.vo_r:List[PartitionIntersectionVO] = []
        self.common_part_vo_s:List[List[PartitionIntersectionVO]] = []
        self.non_overlap_vo_s:List[List[PartitionIntersectionVO]] = []
        self.keyword_order:List[bytes] = []
        self.set_sizes:List[int] = []
        
    def vo_size(self)->int:
        size = 8
        for v in self.vo_r:
            size += 8 + v.vo_size()
        size += 8
        for v in self.common_part_vo_s:
            for x in v:
                size += 8 + x.vo_size()
        size += 8
        for v in self.non_overlap_vo_s:
            for x in v:
                size += 8 + x.vo_size()
        size += 8 + len(self.keyword_order) * len(self.keyword_order[0])
        size += 8 + len(self.set_sizes) * 8
        return size

def generate_multikeyword_partition_intersection_vo(dataset:Dict[bytes, List[bytes]], ads:Dict[bytes, List[PartitionADS]], keywords:List[bytes], prefix_lens:List[int]) -> MultiKeywordVerificationObject:
    """生成多关键词的验证对象"""
    #assert(len(keywords) >= 3)
    vo = MultiKeywordVerificationObject()
    ordered_keywords = sorted(keywords, key=lambda k: len(dataset[k]))
    vo.keyword_order = ordered_keywords
    for k in vo.keyword_order:
        vo.set_sizes.append(len(dataset[k]))
    print(f"生成证明的关键词顺序:{ordered_keywords}")
    # 生成R的存在性证明
    keyword_r = ordered_keywords[0]
    r = dataset[ordered_keywords[0]]
    vo.vo_r = generate_partition_intersection_vo_r_part(ads[keyword_r], r, dataset[ordered_keywords[1]], prefix_lens)
    print(f"已生成R部分的证明")
    # 进行交集计算
    result = set(r)
    for k in ordered_keywords[1:]:
        result.intersection_update(dataset[k])
    result = sorted(list(result))
    print(f"交集计算结果长度:{len(result)}")
    # 为交集计算结果生成验证对象
    if len(result) > 0:
        for k in ordered_keywords[1:]:
            s_vo = generate_partition_intersection_vo_s_part(ads[k], result, dataset[k], prefix_lens)
            vo.common_part_vo_s.append(s_vo)
    # 为非交集结果生成验证对象
    remained_elements = set(r).difference(result)
    count = 0
    for k in ordered_keywords[1:]:
        s = dataset[k]
        non_overlap_elements = remained_elements.difference(s)
        non_overlap_elements = sorted(list(non_overlap_elements))
        if len(non_overlap_elements) == 0:
            vo.non_overlap_vo_s.append([])
            continue
        s_vo = generate_partition_intersection_vo_s_part(ads[k], non_overlap_elements, s, prefix_lens)
        assert(len(s_vo) > 0)
        vo.non_overlap_vo_s.append(s_vo)
        remained_elements.difference_update(non_overlap_elements)
        print(f"当前轮不相交元素数量{len(non_overlap_elements)}, 剩余元素数量{len(remained_elements)}")
        count += 1
        if len(remained_elements) == 0:
            break
    assert(len(remained_elements) == 0)
    print(f"S证明生成轮数:{count}")
    return vo


def verify_partition_intersection_vo_r_part(r_vo:List[PartitionIntersectionVO], pk:bytes, r_key:bytes, prefix_lens:List[int]) -> bool:
    """校验R集合验证对象的完备性"""
    # 对于R的每一个分区R_i, 验证分区验证对象VO.R[i], 提取对应子集r_i.
    print(f"正在校验R集合验证对象...")
    total_replayed_r = set()
    for i in range(len(r_vo)):
        part = r_vo[i]
        length = part.seg_size
        sk = pk + bytes(r_key) + b'|' + length.to_bytes(8, 'big') + b'|' + part.left + b'|' + part.right + i.to_bytes(8, 'big')
        print(f"  验证R集合区间{i}: {part.left} - {part.right}")
        replayed_r = set()
        for l in part.mct_vo.keys():
            print(f"  验证R集合VO前缀{l}")
            r_mct = part.mct_vo[l]
            flag, r_l, _ = r_mct.verify(sk, [])
            if not flag:
                print(f"  R集合前缀{l}验证失败.")
                return False, f"R集合前缀{l}验证失败.", None
            replayed_r.update(r_l)
        # 合并replayed_r中出现的元素(消除所有的低前缀长度子串)
        tmp_l = list(replayed_r)
        tmp_l.sort()
        for i in range(len(tmp_l)):
            l = len(tmp_l[i])
            if tmp_l[i][0:l] == LEFT_BOUND[0:l] or tmp_l[i][0:l] == RIGHT_BOUND[0:l]:
                replayed_r.remove(tmp_l[i])
            elif i +1 < len(tmp_l) and tmp_l[i][0:l] == tmp_l[i+1][0:l]:
                replayed_r.remove(tmp_l[i])
        # 验证区间集合的长度
        if len(replayed_r)!= part.seg_size:
            print(f"  验证R集合VO长度失败: {len(replayed_r)} vs. {part.seg_size}.")
            return False, "R集合VO长度验证失败.", None
        print(f"  重放R集合元素数量: {len(replayed_r)}")
        total_replayed_r.update(replayed_r)
    # 验证VO.R中的区间覆盖完整性.
    for i in range(len(r_vo)):
        if i == 0:
            continue
        if r_vo[i-1].right != r_vo[i].left:
            print(f"  验证R集合VO区间{i}覆盖失败.")
            return False, "R集合VO区间覆盖验证失败.", None
    if r_vo[-1].right != RIGHT_BOUND:
        print(f"  验证R集合VO区间[-1]覆盖失败.")
        return False, "R集合VO区间[-1]覆盖验证失败.", None
    print(f"  重放R集合长度{len(total_replayed_r)}")
    return True, None, total_replayed_r

def verify_partition_intersection_vo_s_part(s_vo:List[PartitionIntersectionVO], pk:bytes, s_key:bytes) -> bool:
    #对于VO.S的每一个涉及到的分区S_i, 验证分区验证对象VO.S[i].
    replayed_s_intervals:Dict[int, Set[Tuple[bytes, bytes]]] = {}
    for part in s_vo:
        sk = pk + bytes(s_key) + b'|' + part.seg_size.to_bytes(8, 'big') + b'|' + part.left + b'|' + part.right + part.idx.to_bytes(8, 'big')
        part_s_intervals = set()
        for l in part.mct_vo.keys():
            s_mct = part.mct_vo[l]
            if s_mct is None:
                continue
            flag, s_l, _ = s_mct.verify(sk, [])
            if not flag:
                print(f"S集合前缀{l}的MCT验证失败.")
                return False, f"S集合前缀{l}验证失败.", None
            known_leafs: Dict[int, bytes] = {}
            for tuple in s_mct.chain:
                known_leafs[tuple[3]] = tuple[0]
                known_leafs[tuple[3]+1] = tuple[1]
            for node_id in s_mct.tree:
                if node_id >= part.seg_size + 2:
                    continue
                known_leafs[node_id] = s_mct.tree[node_id]
            known_leafs[0] = part.left
            known_leafs[part.seg_size + 1] = part.right
            for node_id in known_leafs:
                if node_id + 1 in known_leafs:
                    part_s_intervals.add((known_leafs[node_id], known_leafs[node_id+1]))
        replayed_s_intervals[part.idx] = part_s_intervals
        for l in part.bf_vo.keys():
            if part.bf_vo[l] is None:
                continue
            raw_bytes = part.bf_vo[l].bit_array.tobytes()
            sig = hmac.new(sk, raw_bytes, sha256).digest()
            if sig != part.bf_vo[l].signature:
                print(f"S集合前缀{l}的BF验证失败.")
                return False, f"S集合前缀{l}的BF验证失败.", None
    return True, None, replayed_s_intervals

def verify_intersection_result(result:Set[bytes], replayed_r:List[bytes], s_vo:List[PartitionIntersectionVO], replay_s_intervals:Dict[int, Set[Tuple[bytes, bytes]]]) -> Tuple[bool, str]:
    """对于R'中的每一个元素x, 验证x在S'中的存在性, 应能明确获得x是否存在的证据. """
    replayed_result = set()
    for x in replayed_r:
        # 定位x在s中的区间
        spart = None
        for p in s_vo:
            if p.left <= x and x < p.right:
                spart = p
            if p.idx == 0 and x < p.left:
                spart = p
        if spart is None:
            print(f"  元素{x}没有在S的证明中找到对应区间")
            return False, f"元素{x}没有在S的证明中找到对应区间"
        if spart.idx == 0 and x < spart.left:
            continue # 在集合S之前出现的元素,直接超出左边界,不可能出现在交集中
        # 检查x在s中的存在性, 如果存在则加入replayed_result
        if len(spart.bf_vo) == 0:
            mct_check = True
        else:
            mct_check = False # 是否要进行mct_check
        for l in spart.bf_vo:
            if spart.bf_vo[l] is None:
                continue
            if x[0:l] in spart.bf_vo[l]:
                mct_check = True
        if not mct_check:
            continue # 如果无须mct_check, 则不必加入交集计算结果
        s_intervals = replay_s_intervals[spart.idx]
        s_tuple = None
        for t in s_intervals:
            if t[0] <= x and x <= t[1]:
                if s_tuple is None:
                    s_tuple = t
                elif len(t[0]) > len(s_tuple[0]):
                    s_tuple = t
        if s_tuple is None:
            print(f"  元素{x}未在S集合中找出覆盖区间.")
            return False, f"元素{x}未在S集合中找出覆盖区间."
        if s_tuple[0] == x or x == s_tuple[1]:
            replayed_result.add(x)
    # 比较result和reaplyed_result,两者应该完全一致
    if len(replayed_result) != len(result) or len(replayed_result.intersection(result)) != len(result):
        print(f"  重放出的集合与计算结果不一致, 验证失败.")
        return False, "重放出的集合与计算结果不一致."
    return True, None

def verify_intersection_status(replayed_r:Set[bytes], s_vo:List[PartitionIntersectionVO], replay_s_intervals:Dict[int, Set[Tuple[bytes, bytes]]]) -> Tuple[bool, str, Set[bytes], Set[bytes], Set[bytes]]:
    common_elements = set()
    non_overlap_elements = set()
    unknown_elements = set()
    for x in replayed_r:
        # 定位x在s中的区间
        spart = None
        for p in s_vo:
            if p.left <= x and x < p.right:
                spart = p
            if p.idx == 0 and x < p.left:
                spart = p
        if spart is None:
            print(f"  元素{x}没有在S的证明中找到对应区间")
            return False, f"元素{x}没有在S的证明中找到对应区间", None, None, None
        if spart.idx == 0 and x < spart.left:
            non_overlap_elements.add(x)
            continue # 在集合S之前出现的元素,直接超出左边界,不可能出现在交集中
        # 检查x在s中的存在性, 如果存在则加入replayed_result
        if len(spart.bf_vo) == 0:
            mct_check = True
        else:
            mct_check = False # 是否要进行mct_check
        for l in spart.bf_vo:
            if spart.bf_vo[l] is None:
                continue
            if x[0:l] in spart.bf_vo[l]:
                mct_check = True
        if not mct_check:
            non_overlap_elements.add(x)
            continue # 如果无须mct_check, 则不必加入交集计算结果
        s_intervals = replay_s_intervals[spart.idx]
        s_tuple = None
        for t in s_intervals:
            if t[0] <= x and x <= t[1]:
                if s_tuple is None:
                    s_tuple = t
                elif len(t[0]) > len(s_tuple[0]):
                    s_tuple = t
        if s_tuple is None:
            # 无法找到可证明的区间
            unknown_elements.add(x)
        elif s_tuple[0] == x or x == s_tuple[1]:
            common_elements.add(x)
        else:
            non_overlap_elements.add(x)
    return True, "OK", common_elements, non_overlap_elements, unknown_elements

def verify_multikey_intersection_results(vo:MultiKeywordVerificationObject, prefix_lens:List[int], pk:bytes, result:List[bytes]) -> Tuple[bool, str]:
    ordered_keywords = vo.keyword_order
    vo_r = vo.vo_r
    flag, msg, replayed_r = verify_partition_intersection_vo_r_part(vo_r, pk, ordered_keywords[0], prefix_lens)
    if not flag:
        return False, "基础R集合验证失败:"+msg
    if len(replayed_r) != vo.set_sizes[0]:
        return False, "R集合长度验证失败"
    print("R已经得到验证")
    replayed_common_elements = set(replayed_r)
    for i in range(len(ordered_keywords[1:])):
        s_key = ordered_keywords[i+1]
        if i >= len(vo.common_part_vo_s):
            break # 没有相关证明
        s_vo = vo.common_part_vo_s[i]
        flag, msg, replayed_s_intervals = verify_partition_intersection_vo_s_part(s_vo, pk, s_key)
        if not flag:
            return False, "非空交集证明验证失败:"+msg
        flag, msg, common_elements, non_overlap_elements, unknown_elements = verify_intersection_status(replayed_r, s_vo, replayed_s_intervals)
        if not flag:
            return False, "非空交集计算结果验证失败:"+msg
        replayed_common_elements.intersection_update(common_elements)
    print(f"非空交集计算结果已得到验证")
    is_empty_result = len(result) == 0 and len(vo.common_part_vo_s) == 0
    if not is_empty_result and replayed_common_elements != set(result):
        print("重放交集计算结果与现有给出的答案不同!")
        return False, "非空交集计算结果验证失败" 
    # 校验其他元素的非存在性证明
    remain_elements = set(replayed_r).difference(result)
    for i in range(len(vo.non_overlap_vo_s)):
        s_key = ordered_keywords[i+1]
        s_vo = vo.non_overlap_vo_s[i]
        if len(s_vo) == 0:
            continue # 跳过当前关键词
        flag, msg, replayed_s_intervals = verify_partition_intersection_vo_s_part(s_vo, pk, s_key)
        if not flag:
            return False, "非相交证明验证失败:"+msg
        flag, msg, common_elements, non_overlap_elements, unknown_elements = verify_intersection_status(remain_elements, s_vo, replayed_s_intervals)
        if not flag:
            return False, "非相交交集计算结果验证失败:"+msg
        remain_elements.difference_update(non_overlap_elements)
        print(f"剩余{len(remain_elements)}元素待证明")
    if len(remain_elements) != 0:
        return False, "存在部分元素无法验证其存在性"
    print(f"集合非相交性证明已校验")
    return True, "OK"

def test_generate_partition_ads():
    import random
    keys = [1, 2, 3]
    sets = {bytes(1): random.sample(range(1, 5000000), 100), 
            bytes(2): random.sample(range(1, 5000000), 1000)}
    pk = b'\x01' * 32
    ads = generate_partition_ads(sets, pk, [4, 32], 27, 0.1)
    print(len(ads))
# test_generate_partition_ads()
# %%


def calculate_total_vo_size(r_vo:List[PartitionIntersectionVO], s_vo:List[PartitionIntersectionVO]):
    r_size = 0
    for part in r_vo:
        r_size += 8 + part.vo_size()
    print(f"R VO Size: {r_size}")
    s_size = 0
    for part in s_vo:
        s_size += 8 + part.vo_size()
    print(f"S VO Size: {s_size}")
    return 16 + r_size + s_size

def random_hash_set(upperbound:int, num:int):
    import random
    s = [sha256(x.to_bytes(8, 'big')).digest() for x in random.sample(range(1, upperbound), num)]
    if LEFT_BOUND in s:
        s.remove(LEFT_BOUND)
    if RIGHT_BOUND in s:
        s.remove(RIGHT_BOUND)
    s.sort()
    return s

def test_partition_intersection():
    import random
    #random.seed(42)
    keys = [1, 2, 3]
    sets = {bytes(1): random_hash_set(500000, 100), 
            bytes(2): random_hash_set(500000, 10000)}
    pk = b'\x01' * 32
    ads = generate_partition_ads(sets, pk, [4, 32], 200000, 0.1)
    r_vo, s_vo = generate_partition_intersection_vo(sets, ads, bytes(1), bytes(2), [4, 32])
    flag, msg, replayed_r = verify_partition_intersection_vo_r_part(r_vo, pk, bytes(1), [4, 32])
    print(flag)
    assert flag
    flag, msg, replayed_s_intervals = verify_partition_intersection_vo_s_part(s_vo, pk, bytes(2))
    print(flag)
    assert flag
    vo_cost = calculate_total_vo_size(r_vo, s_vo)
    print(vo_cost)
    result = set(sets[bytes(1)]).intersection(sets[bytes(2)])
    flag, msg = verify_intersection_result(result, replayed_r, s_vo, replayed_s_intervals)
    print(flag)
    assert flag

def read_set(set_file_path:str) -> List[bytes]:
    s = []
    with open(set_file_path, "r") as f:
        for line in f:
            s.append(sha256(line.strip().encode('utf-8')).digest())
    s.sort()
    return s

def calculate_ads_size(ads:Dict[bytes, List[PartitionADS]]):
    size = 0
    for k in ads:
        size += len(k)
        for part in ads[k]:
            size += 8 + part.vo_size()
    return size

import cProfile
import pstats

def test_partition_intersection():
    import random
    #random.seed(42)
    keys = [1, 2, 3]
    sets = {bytes(1): random_hash_set(500000, 1000), 
            bytes(2): random_hash_set(500000, 100000)}
    pk = b'\x01' * 32
    ads = generate_partition_ads(sets, pk, [4, 32], 200000, 0.1)
    generate_partition_intersection_vo(sets, ads, bytes(1), bytes(2), [4, 32])
    r_vo, s_vo = generate_partition_intersection_vo(sets, ads, bytes(1), bytes(2), [4, 32])
    flag, msg, replayed_r = verify_partition_intersection_vo_r_part(r_vo, pk, bytes(1), [4, 32])
    print(flag)
    assert flag
    flag, msg, replayed_s_intervals = verify_partition_intersection_vo_s_part(s_vo, pk, bytes(2))
    print(flag)
    assert flag
    vo_cost = calculate_total_vo_size(r_vo, s_vo)
    print(vo_cost)
    result = set(sets[bytes(1)]).intersection(sets[bytes(2)])
    flag, msg = verify_intersection_result(result, replayed_r, s_vo, replayed_s_intervals)
    print(flag)
    assert flag


def test_multikeyword_intersection(seed:int):
    import random
    random.seed(seed)
    keys = [x.to_bytes(8) for x in list(range(5))]
    sets = {}
    for k in keys:
        sets[k] = random_hash_set(10000, 500)
    pk = b'\x01' * 32
    ads = generate_partition_ads(sets, pk, [4, 32], 200000, 0.1)
    query_keywords = keys[0:3]
    result = set(sets[query_keywords[0]])
    for k in query_keywords[1:]:
        result.intersection_update(sets[k])
    result = sorted(list(result))
    print(f"交集计算结果长度:{len(result)}")
    vo = generate_multikeyword_partition_intersection_vo(sets, ads, query_keywords, [4,32])
    flag, msg = verify_multikey_intersection_results(vo, [4,32], pk, result)
    assert flag
    if len(result) > 0:
        # 对result进行篡改
        # 将result中随机一个元素删除
        random_idx = random.randint(0, len(result)-1)
        modified_result = result.copy()
        print(f"随机删除元素{result[random_idx]}")
        modified_result.remove(modified_result[random_idx])
        flag, msg = verify_multikey_intersection_results(vo, [4,32], pk, modified_result)
        assert not flag
        print(f"确实验证失败, 原因:{msg}")
    random_idx = random.randint(0, len(sets[query_keywords[0]])-1)
    element = sets[query_keywords[0]][random_idx]
    if not element in result:
        modified_result = result.copy()
        modified_result.append(element)
        modified_result.sort()
        flag, msg = verify_multikey_intersection_results(vo, [4,32], pk, modified_result)
        assert not flag
        print(f"确实验证失败, 原因:{msg}")
    print(f"验证对象规模：", vo.vo_size())

def random_hash_set_exp(num_elements:int):
    import numpy as np
    range_high = 2 ** 50
    rd = np.random.exponential(scale=1.0, size=num_elements) * range_high / 2
    rd = rd.astype(np.int64) + 1
    result = set(rd)
    while (len(result) < num_elements):   
        result.add(int(np.random.exponential(scale=1.0)))
    s = [sha256(int(x).to_bytes(8, 'big')).digest() for x in result]
    if LEFT_BOUND in s:
        s.remove(LEFT_BOUND)
    if RIGHT_BOUND in s:
        s.remove(RIGHT_BOUND)
    s.sort()
    return s

sets = {}
def keyword_scalability_test():
    import time
    for num_keyword in [3,4,5,6,7,8,9,10]:
        keys = [x.to_bytes(8, 'big') for x in list(range(num_keyword))]
        for k in keys:
            sets[k] = random_hash_set(100000000, 10000)
        pk = b'\x01' * 32
        t1 = time.time()
        ads = generate_partition_ads(sets, pk, [4, 32], 2000000, 0.1)
        t2 = time.time()
        query_keywords = keys
        result = set(sets[query_keywords[0]])
        for k in query_keywords[1:]:
            result.intersection_update(sets[k])
        result = sorted(list(result))
        t3 = time.time()
        vo = generate_multikeyword_partition_intersection_vo(sets, ads, query_keywords, [4,32])
        t4 = time.time()
        flag, msg = verify_multikey_intersection_results(vo, [4,32], pk, result)
        t5 = time.time()
        size = vo.vo_size()
        assert flag
        print(f"=====> NumKeyword: {num_keyword}, ads_time(s): {t2-t1} , vo_generation_time(s): {t4-t3} , vo_size: {size}, vo_verification_time(s): {t5-t4}")      

def length_scalability_test1():
    # 最短部分不变，变化长的部分
    import time
    for L in [1000, 1000, 1000, 5000, 10000, 100000, 1000000, 10000000]:
        keys = [x.to_bytes(8, 'big') for x in [0,1]]
        sets.clear()
        sets[keys[0]] = random_hash_set_exp(1000)
        sets[keys[1]] = random_hash_set_exp(L)
        pk = b'\x01' * 32
        t1 = time.time()
        ads = generate_partition_ads(sets, pk, [4, 32], 50000000, 0.1)
        t2 = time.time()
        query_keywords = keys
        result = set(sets[query_keywords[0]])
        for k in query_keywords[1:]:
            result.intersection_update(sets[k])
        result = sorted(list(result))
        t3 = time.time()
        vo = generate_multikeyword_partition_intersection_vo(sets, ads, query_keywords, [4,32])
        t4 = time.time()
        flag, msg = verify_multikey_intersection_results(vo, [4,32], pk, result)
        t5 = time.time()
        size = vo.vo_size()
        assert flag
        print(f"=====> Mode1: 1000 - {L} , ads_time(s): {t2-t1} , vo_generation_time(s): {t4-t3} , vo_size: {size}, vo_verification_time(s): {t5-t4}", flush=True)      

def length_scalability_test2():
    # 最长部分不变，变化短的部分
    import time
    keys = [x.to_bytes(8, 'big') for x in [0,1]]
    sets.clear()
    sets[keys[1]] = random_hash_set_exp(10000000)
    t00 = time.time()
    pk = b'\x01' * 32
    ads = generate_partition_ads(sets, pk, [4,32], 50000000, 0.1)
    t01 = time.time()
    for L in [1000, 1000, 1000, 5000, 10000, 100000, 1000000, 10000000]:
        tsets = {}
        tsets[keys[0]] = random_hash_set_exp(L)
        t1 = time.time()
        tads = generate_partition_ads(tsets, pk, [4, 32], 50000000, 0.1)
        t2 = time.time()
        sets[keys[0]] = tsets[keys[0]]
        ads[keys[0]] = tads[keys[0]]
        query_keywords = keys
        result = set(sets[query_keywords[0]])
        for k in query_keywords[1:]:
            result.intersection_update(sets[k])
        result = sorted(list(result))
        t3 = time.time()
        vo = generate_multikeyword_partition_intersection_vo(sets, ads, query_keywords, [4,32])
        t4 = time.time()
        flag, msg = verify_multikey_intersection_results(vo, [4,32], pk, result)
        t5 = time.time()
        size = vo.vo_size()
        assert flag
        print(f"=====> Mode2: {L} - 10000000 , ads_time(s): {t2-t1 + t01-t00} , vo_generation_time(s): {t4-t3} , vo_size: {size}, vo_verification_time(s): {t5-t4}", flush=True)      

def length_scalability_test():
    import time
    #for N in [1,2,3]:
    #    for L in [1000, 1000, 1000, 5000, 10000, 100000, 1000000, 10000000]:
    for N in [1,]:
        for L in [1000, 1000, 1000, 1000,1000,1000,1000,1000,1000]:
            keys = [x.to_bytes(8, 'big') for x in list(range(N+1))]
            sets.clear()
            sets[keys[0]] = random_hash_set_exp(1000)
            for i in range(1,N+1):
                sets[keys[i]] = random_hash_set_exp(L)
            pk = b'\x01' * 32
            t1 = time.time()
            ads = generate_partition_ads(sets, pk, [4, 32], 50000000, 0.1)
            t2 = time.time()
            query_keywords = keys
            result = set(sets[query_keywords[0]])
            for k in query_keywords[1:]:
                result.intersection_update(sets[k])
            result = sorted(list(result))
            t3 = time.time()
            vo = generate_multikeyword_partition_intersection_vo(sets, ads, query_keywords, [4,32])
            t4 = time.time()
            flag, msg = verify_multikey_intersection_results(vo, [4,32], pk, result)
            t5 = time.time()
            size = vo.vo_size()
            assert flag
            print(f"=====> N: {N} , length: {L} , ads_time(s): {t2-t1} , vo_generation_time(s): {t4-t3} , vo_size: {size}, vo_verification_time(s): {t5-t4}")      

def loop_test():
    for i in range(5000):
        test_multikeyword_intersection(i)
    
#loop_test()
if __name__ == "__main__":
    import sys
    if sys.argv[1] == "length":
        length_scalability_test()
        #length_scalability_test1()
        #length_scalability_test2()
    elif sys.argv[1] == "keyword":
        keyword_scalability_test()
#cProfile.run('loop_test()', 'profile_results.prof')
    #cProfile.run('test_partition_intersection()', 'profile_results')
    #cProfile.run('test_partition_intersection()')
    #p = pstats.Stats('profile_results')
    #p.sort_stats('cumulative').print_stats()
    
    
