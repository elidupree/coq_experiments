use std::collections::HashMap;
use std::sync::Arc;
use std::time::Instant;
use ordered_float::OrderedFloat;

id_type!(QuestionFamilyId);
id_type!(EnsembleId);
id_type!(ComponentId);

struct Component {
    question_family: QuestionFamilyId,
    dependencies:Vec< ComponentId >
    behavior:
}

struct ComponentEvaluationContext{


}

impl ComponentEvaluationContext {
    fn get (&mut self)
}

trait ComponentBehavior{

}

enum Component {
}

struct TrackedOptimizer{
    expenditures: f64,
    behavior: Arc<OptimizerBehavior>,
}
trait OptimizerBehavior {
    fn step(&self,context: &mut SoupOptimiziationStepContext);
}

struct Ensemble {
    target_cost: f64,
    current_cost: f64,
    question_family: QuestionFamilyId,
    direct_members: Vec<ComponentId>,
}

struct QuestionFamily {
    ensembles: HashMap<EnsembleId, Ensemble>,
}

struct Soup {
    components:HashMap<ComponentId, Component>,
    ensembles:Vec<Ensemble>,
    optimizers: Vec<TrackedOptimizer>,
    //caches:HashMap <CashId,Value >,
}

struct SoupOptimiziationStepContext< 'a> {
    soup: &'a mut Soup,
    optimizer_index:usize,
    cache_query_durations:f64,
}

impl Soup {
    pub fn step (&mut self){
        let chosen_index =self.optimizers.iter().enumerate().min_by_key (|(_,o)| OrderedFloat (o.expenditures)).unwrap().0;
        let chosen_behavior =self.optimizers[chosen_index].behavior.clone()
        let start = Instant::now();
        let context =SoupOptimiziationStepContext {soup:self,optimizer_index:chosen_index};
        chosen_behavior.step (&mut context,);
        let total_duration = start.elapsed().as_secs_f64();
        let unaccounted_expenditure = total_duration - context.cache_query_durations;
        self.optimizers[chosen_index].expenditures += unaccounted_expenditure;
    }
}

impl SoupOptimizationStepContext {

}

struct AllEnsemblesGradientDescentOptimizer;
impl OptimizerBehavior for AllEnsemblesGradientDescentOptimizer {
    fn step(&self, context: &mut SoupOptimiziationStepContext) {
        todo!()
    }
}