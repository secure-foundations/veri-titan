// module SetOfMaps {
//     predicate {:opaque} keysDisjoint<K, V>(ms: set<map<K, V>>)
//     {
//         forall m1, m2 | (m1 in ms && m2 in ms && m1 != m2)
//             :: m1.Keys !! m2.Keys
//     }

//     function flattenMaps<K,V>(ms: set<map<K, V>>): map<K, V>
//         requires keysDisjoint(ms)
//     {
//         reveal keysDisjoint();
//         map m, k | (m in ms && k in m) :: k := m[k]
//     }

//     lemma flattenMapsElemSufLemma<K,V>(ms: set<map<K, V>>, k: K)
//         returns (m: map<K, V>)
//         requires keysDisjoint(ms)
//         requires k in flattenMaps(ms)
//         ensures m in ms && k in m
//         ensures m[k] == flattenMaps(ms)[k]
//     {
//         reveal keysDisjoint();
//         m :| m in ms && k in m;
//         assert flattenMaps(ms)[k] == m[k];
//     }

//     lemma flattenMapsElemNecLemma<K,V>(ms: set<map<K, V>>, m: map<K, V>, k: K)
//         requires keysDisjoint(ms)
//         requires m in ms && k in m
//         ensures k in flattenMaps(ms)
//         ensures m[k] == flattenMaps(ms)[k]
//     {
//     }

//     lemma flattenMapsUpdateLemma<K,V>(ms: set<map<K, V>>, ms': set<map<K, V>>,
//         n: map<K,V>, n': map<K,V>, k: K, v: V)
//         requires keysDisjoint(ms)
//         requires keysDisjoint(ms')
//         requires n in ms
//         requires n' in ms'
//         requires ms' == ms - {n} + {n'}
//         requires k in n
//         requires k in n'
//         requires n'[k] == v
//         requires n' == n[k := v]
//         ensures flattenMaps(ms') == flattenMaps(ms)[k := v]
//     {
//         reveal keysDisjoint();
//         var m := flattenMaps(ms);
//         var m' := flattenMaps(ms');

//         forall key | key in m'
//             ensures key in m
//             ensures key != k ==> m[key] == m'[key]
//             ensures key == k ==> m[key] == n'[key]
//         {
//             var _ := flattenMapsElemSufLemma(ms, key);
//             var _ := flattenMapsElemSufLemma(ms', key);
//         }

//         assert m' == m[k := v];
//     }
// }

// module bytes_seq refines LittleEndianNat {
//     function method BASE(): nat
//     {
//         256
//     }
// }