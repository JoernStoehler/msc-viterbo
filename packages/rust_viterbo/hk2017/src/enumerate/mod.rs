//! Permutation enumeration strategies for the HK2017 algorithm.
//!
//! The algorithm needs to enumerate permutations of facets. Two strategies are provided:
//!
//! - **Naive**: Enumerate all subset permutations of facets. Complexity O(F!).
//! - **Graph-pruned**: Build a facet transition graph and enumerate only valid cycles.
//!   Complexity depends on graph structure, typically much better than O(F!).

pub mod graph;
pub mod naive;

use crate::types::{EnumerationStrategy, FacetData};

/// A permutation of facet indices representing a potential closed orbit.
///
/// The permutation [i0, i1, ..., ik-1] means the orbit visits facets in that order:
/// F_{i0} -> F_{i1} -> ... -> F_{ik-1} -> F_{i0}
pub type Permutation = Vec<usize>;

/// Trait for permutation enumeration strategies.
pub trait PermutationEnumerator {
    /// Generate all permutations to check.
    fn enumerate(&self, facet_data: &FacetData) -> Vec<Permutation>;

    /// Name of the strategy for logging/debugging.
    fn name(&self) -> &'static str;
}

/// Create an enumerator for the given strategy.
pub fn create_enumerator(strategy: EnumerationStrategy) -> Box<dyn PermutationEnumerator> {
    match strategy {
        EnumerationStrategy::Naive => Box::new(naive::NaiveEnumerator),
        EnumerationStrategy::GraphPruned => Box::new(graph::GraphEnumerator),
    }
}

/// Count the total number of permutations for naive enumeration.
///
/// This is Sum_{k=2}^{F} C(F,k) * k! = Sum_{k=2}^{F} F!/(F-k)!
pub fn count_naive_permutations(num_facets: usize) -> usize {
    let mut count = 0;
    for k in 2..=num_facets {
        // C(F, k) * k! = F! / (F-k)!
        count += factorial_ratio(num_facets, num_facets - k);
    }
    count
}

/// Compute n! / m! = n * (n-1) * ... * (m+1) for n >= m.
fn factorial_ratio(n: usize, m: usize) -> usize {
    if n <= m {
        return 1;
    }
    ((m + 1)..=n).product()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_count_naive_permutations_small() {
        // F=2: only one permutation [0,1] and [1,0] = 2
        assert_eq!(count_naive_permutations(2), 2);

        // F=3:
        // k=2: C(3,2)*2! = 3*2 = 6
        // k=3: C(3,3)*3! = 1*6 = 6
        // Total: 12
        assert_eq!(count_naive_permutations(3), 12);

        // F=4:
        // k=2: C(4,2)*2! = 6*2 = 12
        // k=3: C(4,3)*3! = 4*6 = 24
        // k=4: C(4,4)*4! = 1*24 = 24
        // Total: 60
        assert_eq!(count_naive_permutations(4), 60);
    }

    #[test]
    fn test_factorial_ratio() {
        assert_eq!(factorial_ratio(5, 3), 5 * 4); // 5!/3! = 20
        assert_eq!(factorial_ratio(5, 0), 120); // 5!/0! = 120
        assert_eq!(factorial_ratio(5, 5), 1); // 5!/5! = 1
    }
}
