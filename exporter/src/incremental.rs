//! Discovery cursors retain completed request domains across fixed-point waves.
use super::*;

/// A completed rectangle includes negative ABI matches as well as transfers.
/// Callers advance it only after the whole snapshot succeeds; errors abort
/// export instead of converting a failed pair into a completed answer.
#[derive(Default, Clone, Copy)]
pub(super) struct PairFrontier {
    pub sites: usize,
    pub targets: usize,
    pub pairs: usize,
}
impl PairFrontier {
    pub fn site_start(&self, targets: usize) -> usize {
        if targets == self.targets { self.sites } else { 0 }
    }
    pub fn target_start(&self, site: usize) -> usize {
        if site < self.sites { self.targets } else { 0 }
    }
    pub fn complete(&mut self, sites: usize, targets: usize) {
        assert!(sites >= self.sites && targets >= self.targets);
        self.pairs += (sites - self.sites) * targets + self.sites * (targets - self.targets);
        self.sites = sites;
        self.targets = targets;
    }
    pub fn len(&self) -> usize { self.pairs }
}

#[derive(Default)]
pub(super) struct Casts<'tcx> {
    pub inputs: usize,
    pub pairs: usize,
    pub boxes: usize,
    pub resolutions: HashMap<ty::Ty<'tcx>, ty::Instance<'tcx>>,
    pub rows: Vec<cast_queries::Fact>,
}
#[derive(Default)]
pub(super) struct Abis<'tcx> {
    pub explicit: usize,
    pub events: usize,
    pub completed: HashSet<(ty::Instance<'tcx>, &'tcx ty::List<ty::Ty<'tcx>>)>,
    pub rows: Vec<InstanceAbiFact>,
}
#[derive(Default)]
pub(super) struct Vtables {
    pub allocations: usize,
    pub requests: usize,
    pub upcasts: PairFrontier,
    pub rows: Vec<((u64, Vec<u64>, u64, Vec<u64>), (u64, Vec<u64>), VtableFact)>,
}
#[derive(Default)]
pub(super) struct Virtuals<'tcx> {
    pub allocations: usize,
    pub instances: usize,
    pub virtuals: Vec<(u64, ty::Instance<'tcx>, rustc_hir::def_id::DefId)>,
    pub frontier: PairFrontier,
    pub rows: Vec<VirtualFact>,
    pub resolved: OrderedSet<(ty::Instance<'tcx>, ty::Ty<'tcx>, ty::Instance<'tcx>)>,
    pub transfers: PairFrontier,
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn late_sites_and_targets_are_visited_exactly_once_including_empty_waves() {
        let mut frontier = PairFrontier::default();
        let mut visits = HashMap::new();
        for (sites, targets) in [(2, 0), (2, 3), (4, 3), (4, 5), (4, 5)] {
            for site in frontier.site_start(targets)..sites {
                for target in frontier.target_start(site)..targets {
                    *visits.entry((site, target)).or_insert(0) += 1;
                }
            }
            frontier.complete(sites, targets);
        }
        assert_eq!(visits.len(), 20);
        assert!(visits.values().all(|count| *count == 1));
        assert_eq!(frontier.pairs, 20);
    }
}
