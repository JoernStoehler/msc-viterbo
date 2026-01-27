//! Naive permutation enumeration.
//!
//! Enumerates all subset permutations of facet indices.
//! Complexity: O(F!) where F is the number of facets.

use itertools::Itertools;

use super::{Permutation, PermutationEnumerator};
use crate::types::FacetData;

/// Naive enumerator that generates all subset permutations.
pub struct NaiveEnumerator;

impl PermutationEnumerator for NaiveEnumerator {
    fn enumerate(&self, facet_data: &FacetData) -> Vec<Permutation> {
        enumerate_all_subset_permutations(facet_data.num_facets)
    }

    fn name(&self) -> &'static str {
        "naive"
    }
}

/// Generate all permutations of all subsets of size >= 2.
///
/// For each subset S of {0, ..., n-1} with |S| >= 2, generates all
/// permutations of S.
pub fn enumerate_all_subset_permutations(num_facets: usize) -> Vec<Permutation> {
    let mut perms = Vec::new();

    for k in 2..=num_facets {
        for subset in (0..num_facets).combinations(k) {
            for perm in subset.into_iter().permutations(k) {
                perms.push(perm);
            }
        }
    }

    perms
}

/// Iterator version that doesn't allocate all permutations upfront.
///
/// Useful for very large facet counts where storing all permutations
/// would use too much memory.
pub fn subset_permutations_iter(num_facets: usize) -> impl Iterator<Item = Permutation> {
    (2..=num_facets).flat_map(move |k| {
        (0..num_facets)
            .combinations(k)
            .flat_map(move |subset| subset.into_iter().permutations(k))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_enumerate_2_facets() {
        let perms = enumerate_all_subset_permutations(2);
        // Should have exactly 2 permutations: [0,1] and [1,0]
        assert_eq!(perms.len(), 2);

        let set: HashSet<_> = perms.into_iter().collect();
        assert!(set.contains(&vec![0, 1]));
        assert!(set.contains(&vec![1, 0]));
    }

    #[test]
    fn test_enumerate_3_facets() {
        let perms = enumerate_all_subset_permutations(3);
        // k=2: C(3,2)*2! = 3*2 = 6
        // k=3: C(3,3)*3! = 1*6 = 6
        // Total: 12
        assert_eq!(perms.len(), 12);

        // Check some specific permutations exist
        let set: HashSet<_> = perms.into_iter().collect();
        assert!(set.contains(&vec![0, 1]));
        assert!(set.contains(&vec![1, 0]));
        assert!(set.contains(&vec![0, 2]));
        assert!(set.contains(&vec![0, 1, 2]));
        assert!(set.contains(&vec![2, 1, 0]));
    }

    #[test]
    fn test_enumerate_4_facets_count() {
        let perms = enumerate_all_subset_permutations(4);
        // k=2: C(4,2)*2! = 6*2 = 12
        // k=3: C(4,3)*3! = 4*6 = 24
        // k=4: C(4,4)*4! = 1*24 = 24
        // Total: 60
        assert_eq!(perms.len(), 60);
    }

    #[test]
    fn test_all_permutations_have_valid_indices() {
        let num_facets = 5;
        let perms = enumerate_all_subset_permutations(num_facets);

        for perm in perms {
            // All indices should be < num_facets
            assert!(perm.iter().all(|&i| i < num_facets));

            // No duplicates in a single permutation
            let set: HashSet<_> = perm.iter().collect();
            assert_eq!(set.len(), perm.len());

            // Length >= 2
            assert!(perm.len() >= 2);
        }
    }

    #[test]
    fn test_iterator_matches_vec() {
        let num_facets = 4;
        let vec_perms: Vec<_> = enumerate_all_subset_permutations(num_facets);
        let iter_perms: Vec<_> = subset_permutations_iter(num_facets).collect();

        assert_eq!(vec_perms, iter_perms);
    }
}
